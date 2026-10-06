import RiscvImCompare.Image
import RiscvImCompare.Simulation
import RiscvImCompare.ZDecode
import Flapjack.RiscV.L3.Step.Evaluation
import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Step.FetchTheorems

/-!
# riscv-zkvm as a flapjack target, and the state relation

`zkvmTarget` packages riscv-zkvm's `step` as a `HolAsmTarget`, so that flapjack's
own observable machine semantics (`machineSemHOL`) can be run on top of it.
The only ingredient added on top of riscv-zkvm is the `ok` flag of `ZState`,
which records that `step` trapped (returned `none`); a trapped state is not
`stateOk`, which makes flapjack's evaluator report an error, mirroring how an
L3 exception makes the L3 state not `stateOk`.

`Rel C ms z` relates an L3 state and a riscv-zkvm state. `C` is the set of
instruction addresses of the loaded program: riscv-zkvm fetches instructions
from its separate, fixed `code` map, while L3 fetches the bytes from memory, so
the relation requires the two to agree on `C`.
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

/-- A riscv-zkvm machine state together with a flag that is cleared once
`RiscvZkvm.Rv64.step` has trapped. -/
structure ZState where
  m : MachineState
  ok : Bool

/-- One riscv-zkvm step; a trap keeps the state and clears `ok`. -/
def zNext (z : ZState) : ZState :=
  match RiscvZkvm.Rv64.step z.m with
  | some m' => ⟨m', true⟩
  | none => ⟨z.m, false⟩

/-- A riscv-zkvm state is ok if it has not trapped and its PC is 4-aligned
(the counterpart of `riscvOk`'s alignment conjunct). -/
def zOk (z : ZState) : Bool := z.ok && (z.m.pc.toNat % 4 == 0)

/-- riscv-zkvm's step function as a flapjack `HolAsmTarget`. The assembler
configuration is flapjack's `riscvConfig`: it is only used by the evaluator to
check that the PC points into encoded `asm` instructions. Registers are read
raw (`regs`), the counterpart of L3's raw `c_gpr`. -/
def zkvmTarget : HolAsmTarget 64 ZState Unit where
  config := riscvConfig
  next := zNext
  getPc z := z.m.pc
  getReg z n := z.m.regs (regOfBits (BitVec.ofNat 5 n))
  getFpReg _ _ := 0
  getByte z a := z.m.getByte a
  stateOk := zOk
  proj _ _ := ()

/-- The relation between an L3 state and a riscv-zkvm state. -/
structure Rel (C : BitVec 64 → Prop) (ms : riscv_state) (z : ZState) : Prop where
  ok : riscvOk ms = zOk z
  pc : ms.c_PC ms.procID = z.m.pc
  regs : ∀ r : BitVec 5, ms.c_gpr ms.procID r = z.m.regs (regOfBits r)
  mem : MemRel ms.MEM8 z.m.mem
  code : ∀ a, C a → z.m.code a = decode (l3Word ms.MEM8 a)

/-- No byte of the store `[p, p + n)` hits an instruction of `C`. -/
def NoCodeWrite (C : BitVec 64 → Prop) (p : BitVec 64) (n : Nat) : Prop :=
  ∀ a, C a → ∀ i < 4, ∀ j < n, a + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j

/-- Side condition on an L3 instruction under which riscv-zkvm executes it the
same way: memory accesses must be aligned and inside riscv-zkvm's fixed memory
map (riscv-zkvm traps otherwise, L3 does not), and stores must not modify the
program (riscv-zkvm's code is fixed, L3 executes from memory). -/
def MemSafe (C : BitVec 64 → Prop) (ms : riscv_state) : instruction → Prop
  | .Load (.LD (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidDwordAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | .Load (.LWU (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidMemAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | .Load (.LHU (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidHalfwordAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | .Load (.LBU (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidByteAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | .Store (.SD (rs1, _, off)) =>
    RiscvZkvm.Rv64.isValidDwordAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true ∧
      NoCodeWrite C (GPR rs1 ms + BitVec.signExtend 64 off) 8
  | .Store (.SW (rs1, _, off)) =>
    RiscvZkvm.Rv64.isValidMemAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true ∧
      NoCodeWrite C (GPR rs1 ms + BitVec.signExtend 64 off) 4
  | .Store (.SH (rs1, _, off)) =>
    RiscvZkvm.Rv64.isValidHalfwordAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true ∧
      NoCodeWrite C (GPR rs1 ms + BitVec.signExtend 64 off) 2
  | .Store (.SB (rs1, _, off)) =>
    RiscvZkvm.Rv64.isValidByteAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true ∧
      NoCodeWrite C (GPR rs1 ms + BitVec.signExtend 64 off) 1
  | _ => True

/-- An L3 step is *safe* (for the comparison) if the PC is an instruction
address of the program and the instruction there satisfies `MemSafe`. -/
def SafeL3 (C : BitVec 64 → Prop) (ms : riscv_state) : Prop :=
  C (ms.c_PC ms.procID) ∧ MemSafe C ms (Decode (l3Word ms.MEM8 (ms.c_PC ms.procID)))

/-! ## Basic facts -/

/-- The L3 state right after fetching a 4-byte instruction. -/
def fetched (ms : riscv_state) : riscv_state :=
  { ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip }

theorem holAligned_two_iff (x : BitVec 64) : holAligned 2 x = (x.toNat % 4 == 0) := by
  simp only [holAligned, holAlign_eq_div]
  have hx := x.isLt
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

theorem regOfBits_toNat (a : BitVec 5) : (regOfBits a).toNat = a.toNat := by
  have ha := a.isLt
  simp only [regOfBits]
  generalize a.toNat = x at *
  interval_cases x <;> rfl

theorem regOfBits_injective {a b : BitVec 5} (h : regOfBits a = regOfBits b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← regOfBits_toNat a, ← regOfBits_toNat b, h]

theorem regOfBits_zero_iff (a : BitVec 5) : regOfBits a = .x0 ↔ a = 0 := by
  constructor
  · intro h; exact regOfBits_injective (h.trans (by rfl))
  · rintro rfl; rfl

theorem getReg_of_ne {s : MachineState} {r : RiscvZkvm.Rv64.Reg} (h : r ≠ .x0) :
    s.getReg r = s.regs r := by
  cases r <;> simp_all [MachineState.getReg]

/-- L3's `GPR` (which reads `x0` as zero) agrees with riscv-zkvm's `getReg`. -/
theorem GPR_eq (C : BitVec 64 → Prop) {ms : riscv_state} {z : ZState} (h : Rel C ms z)
    (r : BitVec 5) : GPR r ms = z.m.getReg (regOfBits r) := by
  by_cases hr : r = 0
  · subst hr; rfl
  · have hz : regOfBits r ≠ .x0 := fun e => hr ((regOfBits_zero_iff r).mp e)
    rw [getReg_of_ne hz, ← h.regs r]
    simp only [GPR, gpr, beq_iff_eq]
    split
    · exact absurd ‹_› hr
    · rfl

theorem riscvNext_of_some {ms ms' : riscv_state} (h : Step.NextRISCV ms = some ms') :
    riscvNext ms = ms' := by
  simp [riscvNext, h, holThe]

theorem zNext_of_some {z : ZState} {m' : MachineState} (h : RiscvZkvm.Rv64.step z.m = some m') :
    zNext z = ⟨m', true⟩ := by
  simp [zNext, h]

theorem decode_low_bits (w : BitVec 32) (h : decode w ≠ none) :
    w.getLsbD 0 = true ∧ w.getLsbD 1 = true := by
  have key : (w.extractLsb' 0 7).toNat % 4 = 3 := by
    by_contra hne
    apply h
    unfold decode
    dsimp only
    split
    all_goals first | rfl | omega
  have e : ∀ k, k < 7 → w.getLsbD k = (w.extractLsb' 0 7).getLsbD k := by
    intro k hk; rw [BitVec.getLsbD_extractLsb']; simp [hk]
  rw [e 0 (by omega), e 1 (by omega), BitVec.getLsbD, BitVec.getLsbD]
  generalize (w.extractLsb' 0 7).toNat = n at key
  constructor
  · rw [Nat.testBit, Nat.shiftRight_zero]; simp; omega
  · rw [Nat.testBit, Nat.shiftRight_one]; simp; omega

/-- Encoded instructions have the 32-bit-instruction low bits `11`. -/
theorem encode_low_bits (i : instruction) (h : toZ i ≠ none) :
    (Encode i).getLsbD 0 = true ∧ (Encode i).getLsbD 1 = true :=
  decode_low_bits _ (by rw [decode_encode_toZ i h]; exact h)

end RiscvImCompare
