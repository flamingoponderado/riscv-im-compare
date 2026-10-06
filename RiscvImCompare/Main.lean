/-
Portions of this file (the premises of `panToTargetCompileSemanticsZkvm`) are copied from
Flapjack (BSD 3-Clause License); see LICENSE and LICENSES/flapjack-COPYRIGHT.
-/
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

open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL

/-- **Pancake compiler correctness on riscv-zkvm.** flapjack's
`panToTargetCompileSemanticsRiscV` (Pancake → RISC-V, stated over flapjack's L3
RISC-V model) transferred to the same compiled program running on riscv-zkvm:
every behaviour of the riscv-zkvm machine is a behaviour allowed for the
Pancake source program (up to resource limits). All premises of the flapjack
theorem are kept verbatim; the extra premises are the riscv-zkvm initial
state related to the L3 one, corresponding environment oracles, and that the
L3 run is `SafeL3`. -/
theorem panToTargetCompileSemanticsZkvm {σ : Type}
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (pan_code : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : RiscV.L3.riscv_state) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS)
    -- riscv-zkvm side:
    (C : BitVec 64 → Prop)
    (nextI : Nat → ZState → ZState) (ffiI : Nat → Nat × List (BitVec 8) × ZState → ZState)
    (ccacheI : Nat → BitVec 64 × BitVec 64 × ZState → ZState)
    (hor : OraclesCorr C mc nextI ffiI ccacheI) (z : ZState) (hR : Rel C ms z)
    (hsafe : RunSafe mc ffi (SafeL3 C) ms) :
    isRiscvMachineConfig mc →
    compileProgMax (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig) mc pan_code =
      (some (bytes, bitmaps, c'), stack_max) ∧
    pancakeGoodCodeHOL pan_code = true ∧
    distinctParamsHOL (functionsHOL pan_code) ∧
    ((functionsHOL pan_code).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL pan_code < 2 ^ 64 ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    (0 : BitVec 64) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL pan_code
       let struct_ctxt := decsStcnamesHOLExact (width := 64) [] pan_code
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s pan_code ∧
    heap_len = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (64 / 8) ∧
    s.topAddr = s.baseAddr + (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 heap_len -
      BitVec.ofNat 64 (globals_size * 64 / 8) ∧
    globals_size ≤ heap_len ∧
    s.memaddrs = StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heap_len - globals_size) ∧
    holAligned (wordShiftAmount 64 + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true ∧
    adj_ptr2 = mc.target.getReg ms mc.lenReg +
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
    adj_ptr4 = mc.target.getReg ms mc.len2Reg -
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
    adj_ptr2 ≤ mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.ptr2Reg ≤ adj_ptr4 ∧
    (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64
          (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig).dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig).stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL (zkvmConfig mc nextI ffiI ccacheI) ffi z b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config
          (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig) mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b  := by
  intro hmc hpre b hb
  exact panToTargetCompileSemanticsRiscV mc pan_code bytes bitmaps c' stack_max s ms globals_size
    heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc hpre b
    ((machineSem_l3_iff_zkvm C mc hmc.1 nextI ffiI ccacheI hor ffi ms z hR hsafe b).mpr hb)

/-! ## Related initial states exist -/

/-- A riscv-zkvm state built from an L3 state: the same registers, PC and
memory, and the instructions at the addresses `C` decoded (with riscv-zkvm's
own decoder) from the L3 memory. -/
noncomputable def zOfL3 (C : BitVec 64 → Prop) (ms : riscv_state) : ZState :=
  open Classical in
  { m := { regs := fun r => ms.c_gpr ms.procID (BitVec.ofNat 5 r.toNat)
           mem := fun a => l3Dword ms.MEM8 a
           code := fun a => if C a then decode (l3Word ms.MEM8 a) else none
           pc := ms.c_PC ms.procID }
    ok := riscvOk ms }

theorem rel_zOfL3 (C : BitVec 64 → Prop) (ms : riscv_state) : Rel C ms (zOfL3 C ms) where
  ok := by
    simp only [zOfL3, zOk]
    cases h : riscvOk ms
    · rfl
    · have := ((riscvOk_iff ms).mp h).2.2.2.2
      rw [holAligned_two_iff] at this
      simp [this]
  pc := rfl
  regs := fun r => by
    simp only [zOfL3, regOfBits_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  mem := fun a _ => rfl
  code := fun a ha => by simp [zOfL3, ha]

end RiscvImCompare
