import RiscvImCompare.SimStep
import Flapjack.Pancake.Proofs.PanToTarget.RiscVInstance

/-!
# Main results

* `zkvmConfig` turns flapjack's RISC-V machine configuration into one whose
  processor is riscv-zkvm's `step` (`zkvmTarget`); the environment oracles
  (`nextInterfer`, `ffiInterfer`, `ccacheInterfer`) are supplied for
  riscv-zkvm states.
* `machineSem_l3_iff_zkvm`: the two machines have exactly the same observable
  behaviours (termination outcome + I/O event trace, divergence trace, failure),
  provided the initial states are related, the oracles correspond, and the L3
  run only performs `SafeL3` steps.
* `panToTargetCompileSemanticsZkvm`: flapjack's Pancake compiler-correctness
  theorem for RISC-V, transferred to riscv-zkvm's semantics.
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.RiscVConfig
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

/-- The flapjack machine configuration `mc` with riscv-zkvm as processor and the
given environment oracles over riscv-zkvm states. All other fields (program and
shared address sets, FFI entry points and names, halt and code-cache PCs, MMIO
information, registers used for FFI arguments) are those of `mc`. -/
def zkvmConfig (mc : MachineConfig 64 riscv_state RiscVProjection)
    (nextI : Nat → ZState → ZState) (ffiI : Nat → Nat × List (BitVec 8) × ZState → ZState)
    (ccacheI : Nat → BitVec 64 × BitVec 64 × ZState → ZState) : MachineConfig 64 ZState Unit where
  progAddresses := mc.progAddresses
  sharedAddresses := mc.sharedAddresses
  ffiEntryPcs := mc.ffiEntryPcs
  ffiNames := mc.ffiNames
  ptrReg := mc.ptrReg
  lenReg := mc.lenReg
  ptr2Reg := mc.ptr2Reg
  len2Reg := mc.len2Reg
  ffiInterfer := ffiI
  calleeSavedRegs := mc.calleeSavedRegs
  nextInterfer := nextI
  haltPc := mc.haltPc
  ccachePc := mc.ccachePc
  ccacheInterfer := ccacheI
  target := zkvmTarget
  mmioInfo := mc.mmioInfo

/-- The environment oracles of the two machines correspond: applied to related
states they produce related states. (Like the L3 oracles in flapjack's
compiler theorem, they must in particular leave the program bytes `C` alone.) -/
structure OraclesCorr (C : BitVec 64 → Prop) (mc : MachineConfig 64 riscv_state RiscVProjection)
    (nextI : Nat → ZState → ZState) (ffiI : Nat → Nat × List (BitVec 8) × ZState → ZState)
    (ccacheI : Nat → BitVec 64 × BitVec 64 × ZState → ZState) : Prop where
  next : ∀ n ms z, Rel C ms z → Rel C (mc.nextInterfer n ms) (nextI n z)
  ffi : ∀ n i bs ms z, Rel C ms z → Rel C (mc.ffiInterfer n (i, bs, ms)) (ffiI n (i, bs, z))
  ccache : ∀ n a b ms z, Rel C ms z →
    Rel C (mc.ccacheInterfer n (a, b, ms)) (ccacheI n (a, b, z))

theorem simConfig_zkvm (C : BitVec 64 → Prop) (mc : MachineConfig 64 riscv_state RiscVProjection)
    (htarget : mc.target = riscvTarget)
    (nextI : Nat → ZState → ZState) (ffiI : Nat → Nat × List (BitVec 8) × ZState → ZState)
    (ccacheI : Nat → BitVec 64 × BitVec 64 × ZState → ZState)
    (hor : OraclesCorr C mc nextI ffiI ccacheI) :
    SimConfig mc (zkvmConfig mc nextI ffiI ccacheI) (Rel C) (SafeL3 C) where
  progAddresses := rfl
  sharedAddresses := rfl
  ffiEntryPcs := rfl
  ffiNames := rfl
  ptrReg := rfl
  lenReg := rfl
  ptr2Reg := rfl
  len2Reg := rfl
  haltPc := rfl
  ccachePc := rfl
  mmioInfo := rfl
  config := by rw [htarget]; rfl
  getPc := fun ms z hR => by rw [htarget]; exact hR.pc
  getReg := fun ms z hR => by rw [htarget]; funext n; exact hR.regs _
  getByte := fun ms z hR => by
    rw [htarget]; funext a; exact (getByte_of_memRel hR.mem a).symm
  stateOk := fun ms z hR => by rw [htarget]; exact hR.ok
  next := fun ms z hR hg hs => by
    obtain ⟨hok, -, -, henc⟩ := hg
    rw [htarget] at hok henc ⊢
    exact step_sim C ms z hR hok _ henc hs
  nextInterfer := hor.next
  ffiInterfer := hor.ffi
  ccacheInterfer := hor.ccache

/-- **Behaviour equivalence of flapjack's L3 RISC-V model and riscv-zkvm.**
For a flapjack RISC-V machine configuration `mc` and the same configuration
running on riscv-zkvm, related initial states and corresponding environment
oracles, the two machines have exactly the same `machineSemHOL` behaviours, as
long as every step of the L3 run is `SafeL3` (memory accesses aligned and inside
riscv-zkvm's memory map, stores outside the program, PC inside the program). -/
theorem machineSem_l3_iff_zkvm {σ : Type} (C : BitVec 64 → Prop)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (htarget : mc.target = riscvTarget)
    (nextI : Nat → ZState → ZState) (ffiI : Nat → Nat × List (BitVec 8) × ZState → ZState)
    (ccacheI : Nat → BitVec 64 × BitVec 64 × ZState → ZState)
    (hor : OraclesCorr C mc nextI ffiI ccacheI)
    (ffi : HolFfiState σ) (ms : riscv_state) (z : ZState) (hR : Rel C ms z)
    (hsafe : RunSafe mc ffi (SafeL3 C) ms) (b : HolBehaviour) :
    machineSemHOL mc ffi ms b ↔ machineSemHOL (zkvmConfig mc nextI ffiI ccacheI) ffi z b :=
  machineSem_sim (simConfig_zkvm C mc htarget nextI ffiI ccacheI hor) hR hsafe b

end RiscvImCompare
