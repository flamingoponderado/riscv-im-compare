import RiscvImCompare.L3Step
import RiscvImCompare.Memory

/-!
# Per-instruction lockstep simulation between L3 `NextRISCV` and riscv-zkvm `step`
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

section ZSimp
variable (s : MachineState) (r : RiscvZkvm.Rv64.Reg) (v p : BitVec 64)
@[simp] theorem z_setPC_pc : (s.setPC p).pc = p := rfl
@[simp] theorem z_setPC_regs : (s.setPC p).regs = s.regs := rfl
@[simp] theorem z_setPC_mem : (s.setPC p).mem = s.mem := rfl
@[simp] theorem z_setPC_code : (s.setPC p).code = s.code := rfl
@[simp] theorem z_setReg_pc : (s.setReg r v).pc = s.pc := by cases r <;> rfl
@[simp] theorem z_setReg_mem : (s.setReg r v).mem = s.mem := by cases r <;> rfl
@[simp] theorem z_setReg_code : (s.setReg r v).code = s.code := by cases r <;> rfl
end ZSimp

/-- Re-establishing `Rel` after a successful step on both sides. -/
theorem rel_post {C : BitVec 64 → Prop} {ms : riscv_state} (hok : riscvOk ms = true)
    (ms' : riscv_state) (m' : MachineState)
    (hproc : ms'.procID = ms.procID) (hmcsr : ms'.c_MCSR = ms.c_MCSR)
    (hexc : ms'.exception = .NoException) (hnf : ms'.c_NextFetch ms.procID = none)
    (hpc : ms'.c_PC ms.procID = m'.pc)
    (hregs : ∀ r, ms'.c_gpr ms.procID r = m'.regs (regOfBits r))
    (hmem : MemRel ms'.MEM8 m'.mem)
    (hcode : ∀ a, C a → m'.code a = decode (l3Word ms'.MEM8 a)) :
    Rel C ms' ⟨m', true⟩ := by
  have f := (riscvOk_iff ms).mp hok
  refine ⟨?_, by rw [hproc]; exact hpc, by rw [hproc]; exact hregs, hmem, hcode⟩
  simp only [riscvOk, zOk, hproc, hmcsr, f.1, f.2.1, hnf, hexc, hpc, holAligned_two_iff]
  simp

theorem regs_write {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
    (rd : BitVec 5) (v : BitVec 64) (r : BitVec 5) :
    (if rd = 0 then ms.c_gpr ms.procID r else holUpdate rd v (ms.c_gpr ms.procID) r) =
      (z.m.setReg (regOfBits rd) v).regs (regOfBits r) := by
  by_cases h0 : rd = 0
  · subst h0
    simp only [if_true]
    exact hR.regs r
  · have hz : regOfBits rd ≠ .x0 := fun e => h0 ((regOfBits_zero_iff rd).mp e)
    simp only [h0, if_false, holUpdate]
    have : (z.m.setReg (regOfBits rd) v).regs =
        fun r' => if r' == regOfBits rd then v else z.m.regs r' := by
      unfold MachineState.setReg; split
      · rename_i e; exact absurd e hz
      · rfl
    rw [this]
    by_cases hr : rd = r
    · subst hr; simp
    · have : regOfBits r ≠ regOfBits rd := fun e => hr (regOfBits_injective e).symm
      simp [hr, this, hR.regs r]

/-- Fall-through register write (ALU and load instructions). -/
theorem sim_write {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
    {i : instruction} (h : AtPc ms i) (rd : BitVec 5) (v : BitVec 64)
    (hrun : Run i (fetched ms) = «write'GPR» (v, rd) (fetched ms))
    (hz : RiscvZkvm.Rv64.step z.m = some ((z.m.setReg (regOfBits rd) v).setPC (z.m.pc + 4))) :
    ∃ ms' m', Step.NextRISCV ms = some ms' ∧ RiscvZkvm.Rv64.step z.m = some m' ∧
      Rel C ms' ⟨m', true⟩ := by
  have f := (riscvOk_iff ms).mp h.ok
  refine ⟨_, _, l3_next_normal h _ hrun ?_ ?_, hz, ?_⟩
  · simp only [«write'GPR», «write'gpr», fetched]; split <;> simp [f.2.2.2.1]
  · simp only [«write'GPR», «write'gpr», fetched]; split <;> simp [f.2.2.1]
  · apply rel_post h.ok
    · simp [«write'PC», «write'GPR», «write'gpr», fetched]; split <;> rfl
    · simp [«write'PC», «write'GPR», «write'gpr», fetched]; split <;> rfl
    · simp [«write'PC», «write'GPR», «write'gpr», fetched]; split <;> simp [f.2.2.2.1]
    · simp [«write'PC», «write'GPR», «write'gpr», fetched, holUpdate]; split <;> simp [f.2.2.1]
    · simp only [«write'PC», «write'GPR», «write'gpr», fetched, holUpdate, Skip]
      split <;> simp [hR.pc, holUpdate]
    · intro r
      rw [z_setPC_regs, ← regs_write hR rd v r]
      simp only [«write'PC», «write'GPR», «write'gpr», fetched, holUpdate]
      split <;> simp_all [holUpdate]
    · simp only [«write'PC», «write'GPR», «write'gpr», fetched]
      split <;> simpa using hR.mem
    · intro a ha
      simp only [«write'PC», «write'GPR», «write'gpr», fetched]
      split <;> simpa using hR.code a ha


/-! ### Value identities between the two models' ALU definitions -/

theorem holV2w_bool (b : Bool) : holV2w 64 [b] = if b then 1#64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [holV2w]
  rw [Flapjack.getLsbD_holFcpWord]
  cases b <;> rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rfl
  · simp
  · rfl
  · simp [hpos.ne']

theorem shamt_eq (x : BitVec 64) :
    (BitVec.setWidth 64 (holWordExtract 6 5 0 x)).toNat = x.toNat % 64 := by
  rw [holWordExtract_eq_extractLsb' x 6 5 0 (by omega) (by omega)]
  simp [BitVec.extractLsb'_toNat]
  omega

theorem lui_eq (imm : BitVec 20) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (imm ++ 0#12)) =
      ((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 := by
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
  by_cases h : j < 12 <;> simp [h, hj]

theorem mulhu_eq (a b : BitVec 64) :
    holWordExtract 64 127 64 (BitVec.setWidth 128 a * BitVec.setWidth 128 b) =
      RiscvZkvm.Rv64.rv64_mulhu a b := by
  rw [holWordExtract_eq_extractLsb' _ 64 127 64 (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp [RiscvZkvm.Rv64.rv64_mulhu, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem div_eq (a b : BitVec 64) :
    (if (b == BitVec.ofNat 64 0) = true then BitVec.signExtend 64 (BitVec.ofNat 1 1)
      else BitVec.sdiv a b) = RiscvZkvm.Rv64.rv64_div a b := by
  simp only [RiscvZkvm.Rv64.rv64_div]
  have : BitVec.signExtend 64 (BitVec.ofNat 1 1) = BitVec.allOnes 64 := by decide
  rw [this]

/-- The conclusion of every per-instruction simulation lemma. -/
def StepsAgree (C : BitVec 64 → Prop) (ms : riscv_state) (z : ZState) : Prop :=
  ∃ ms' m', Step.NextRISCV ms = some ms' ∧ RiscvZkvm.Rv64.step z.m = some m' ∧
    Rel C ms' ⟨m', true⟩

theorem sim_write' {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
    {i : instruction} (h : AtPc ms i) (rd : BitVec 5) (v zv : BitVec 64)
    (hrun : Run i (fetched ms) = «write'GPR» (v, rd) (fetched ms))
    (hz : RiscvZkvm.Rv64.step z.m = some ((z.m.setReg (regOfBits rd) zv).setPC (z.m.pc + 4)))
    (hv : v = zv) : StepsAgree C ms z := by
  subst hv; exact sim_write hR h rd v hrun hz

theorem GPR_fetched (r : BitVec 5) (ms : riscv_state) : GPR r (fetched ms) = GPR r ms := rfl
theorem PC_fetched (ms : riscv_state) : PC (fetched ms) = ms.c_PC ms.procID := rfl

theorem in32_fetched {ms : riscv_state} (hok : riscvOk ms = true) :
    in32BitMode () (fetched ms) = (false, fetched ms) := by
  have f := (riscvOk_iff ms).mp hok
  apply Step.in32BitMode_false <;> simp [fetched, f.2.1]

/-- Non-memory riscv-zkvm instruction at the PC. -/
macro "zstep" : tactic => `(tactic| (
  rw [RiscvZkvm.Rv64.step_non_ecall_non_mem ‹_› (by simp) (by simp) rfl]; rfl))

section ALU
variable {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
include hR

theorem sim_ADD (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.ArithR (.ADD (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.ADD (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by simp only [GPR_fetched, GPR_eq C hR])

theorem sim_SUB (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.ArithR (.SUB (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.SUB (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by simp only [GPR_fetched, GPR_eq C hR])

theorem sim_AND (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.ArithR (.AND (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.AND (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by simp only [GPR_fetched, GPR_eq C hR])

theorem sim_OR (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.ArithR (.OR (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.OR (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by simp only [GPR_fetched, GPR_eq C hR])

theorem sim_XOR (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.ArithR (.XOR (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.XOR (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by simp only [GPR_fetched, GPR_eq C hR])

theorem sim_MUL (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.MulDiv (.MUL (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.MUL (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by simp only [GPR_fetched, GPR_eq C hR])

theorem sim_DIV (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.MulDiv (.DIV (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.DIV (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (if (GPR rs2 ms == BitVec.ofNat 64 0) = true then BitVec.signExtend 64 (BitVec.ofNat 1 1)
      else BitVec.sdiv (GPR rs1 ms) (GPR rs2 ms)) _ ?_ (by zstep) ?_
  · by_cases hb : (GPR rs2 ms == BitVec.ofNat 64 0) = true <;> simp [Run, «dfn'DIV», GPR_fetched, hb]
  · rw [div_eq]; simp only [GPR_eq C hR]

theorem sim_MULHU (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.MulDiv (.MULHU (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.MULHU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (holWordExtract 64 127 64 (BitVec.setWidth 128 (GPR rs1 ms) * BitVec.setWidth 128 (GPR rs2 ms)))
    _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'MULHU», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [mulhu_eq]; simp only [GPR_eq C hR]

theorem sim_SLTU (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.ArithR (.SLTU (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.SLTU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (holV2w 64 [BitVec.ult (GPR rs1 ms) (GPR rs2 ms)]) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SLTU», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [holV2w_bool]; simp [GPR_eq C hR]

theorem sim_SLL (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.Shift (.SLL (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.SLL (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (GPR rs1 ms <<< (BitVec.setWidth 64 (holWordExtract 6 5 0 (GPR rs2 ms))).toNat) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SLL», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [shamt_eq]; simp only [GPR_eq C hR]

theorem sim_SRL (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.Shift (.SRL (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.SRL (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (GPR rs1 ms >>> (BitVec.setWidth 64 (holWordExtract 6 5 0 (GPR rs2 ms))).toNat) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SRL», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [shamt_eq]; simp only [GPR_eq C hR]

theorem sim_SRA (rd rs1 rs2 : BitVec 5) (h : AtPc ms (.Shift (.SRA (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.SRA (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (BitVec.sshiftRight (GPR rs1 ms) (BitVec.setWidth 64 (holWordExtract 6 5 0 (GPR rs2 ms))).toNat)
    _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SRA», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [shamt_eq]; simp only [GPR_eq C hR]

theorem sim_SLLI (rd rs1 : BitVec 5) (sh : BitVec 6) (h : AtPc ms (.Shift (.SLLI (rd, rs1, sh))))
    (hc : z.m.code z.m.pc = some (.SLLI (regOfBits rd) (regOfBits rs1) sh)) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (GPR rs1 ms <<< sh.toNat) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SLLI», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false,
      Bool.false_and]
  · simp only [GPR_eq C hR]

theorem sim_SRLI (rd rs1 : BitVec 5) (sh : BitVec 6) (h : AtPc ms (.Shift (.SRLI (rd, rs1, sh))))
    (hc : z.m.code z.m.pc = some (.SRLI (regOfBits rd) (regOfBits rs1) sh)) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (GPR rs1 ms >>> sh.toNat) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SRLI», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false,
      Bool.false_and]
  · simp only [GPR_eq C hR]

theorem sim_SRAI (rd rs1 : BitVec 5) (sh : BitVec 6) (h : AtPc ms (.Shift (.SRAI (rd, rs1, sh))))
    (hc : z.m.code z.m.pc = some (.SRAI (regOfBits rd) (regOfBits rs1) sh)) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (BitVec.sshiftRight (GPR rs1 ms) sh.toNat) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SRAI», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false,
      Bool.false_and]
  · simp only [GPR_eq C hR]

theorem sim_ADDI (rd rs1 : BitVec 5) (imm : BitVec 12) (h : AtPc ms (.ArithI (.ADDI (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.ADDI (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep)
    (by simp only [GPR_fetched, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12])

theorem sim_ANDI (rd rs1 : BitVec 5) (imm : BitVec 12) (h : AtPc ms (.ArithI (.ANDI (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.ANDI (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep)
    (by simp only [GPR_fetched, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12])

theorem sim_ORI (rd rs1 : BitVec 5) (imm : BitVec 12) (h : AtPc ms (.ArithI (.ORI (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.ORI (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep)
    (by simp only [GPR_fetched, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12])

theorem sim_XORI (rd rs1 : BitVec 5) (imm : BitVec 12) (h : AtPc ms (.ArithI (.XORI (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.XORI (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep)
    (by simp only [GPR_fetched, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12])

theorem sim_LUI (rd : BitVec 5) (imm : BitVec 20) (h : AtPc ms (.ArithI (.LUI (rd, imm))))
    (hc : z.m.code z.m.pc = some (.LUI (regOfBits rd) imm)) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (lui_eq imm)

theorem sim_AUIPC (rd : BitVec 5) (imm : BitVec 20) (h : AtPc ms (.ArithI (.AUIPC (rd, imm))))
    (hc : z.m.code z.m.pc = some (.AUIPC (regOfBits rd) imm)) :
    StepsAgree C ms z :=
  sim_write' hR h rd _ _ rfl (by zstep) (by rw [PC_fetched, hR.pc, lui_eq]; rfl)

end ALU

/-! ### Loads -/

theorem aligned8_of_valid {p : BitVec 64} (h : RiscvZkvm.Rv64.isValidDwordAccess p = true) :
    p.toNat % 8 = 0 := by
  simp [RiscvZkvm.Rv64.isValidDwordAccess, RiscvZkvm.Rv64.isAligned8] at h; exact h.2
theorem aligned4_of_valid {p : BitVec 64} (h : RiscvZkvm.Rv64.isValidMemAccess p = true) :
    p.toNat % 4 = 0 := by
  simp [RiscvZkvm.Rv64.isValidMemAccess, RiscvZkvm.Rv64.isAligned4] at h; exact h.2
theorem aligned2_of_valid {p : BitVec 64} (h : RiscvZkvm.Rv64.isValidHalfwordAccess p = true) :
    p.toNat % 2 = 0 := by
  simp [RiscvZkvm.Rv64.isValidHalfwordAccess] at h; exact h.2

section Loads
variable {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
include hR

theorem sim_LD (rd rs1 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Load (.LD (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LD (regOfBits rd) (regOfBits rs1) off))
    (hs : MemSafe C ms (.Load (.LD (rd, rs1, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  have hv : RiscvZkvm.Rv64.isValidDwordAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms) _ ?_
    (by rw [RiscvZkvm.Rv64.step_ld hc hv]; rfl) ?_
  · simp only [Run, «dfn'LD», in32_fetched h.ok, translateAddr, GPR_fetched, Bool.false_eq_true,
      if_false]; rfl
  · rw [GPR_eq C hR] at hs ⊢
    exact (load_ld hR.mem _ (aligned8_of_valid hs)).symm

theorem sim_LWU (rd rs1 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Load (.LWU (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LWU (regOfBits rd) (regOfBits rs1) off))
    (hs : MemSafe C ms (.Load (.LWU (rd, rs1, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  have hv : RiscvZkvm.Rv64.isValidMemAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (BitVec.setWidth 64 (holWordExtract 32 31 0
    (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms))) _ ?_
    (by rw [RiscvZkvm.Rv64.step_lwu hc hv]; rfl) ?_
  · simp only [Run, «dfn'LWU», in32_fetched h.ok, translateAddr, GPR_fetched, Bool.false_eq_true,
      if_false]; rfl
  · rw [GPR_eq C hR] at hs ⊢
    exact (load_lwu hR.mem _ (aligned4_of_valid hs)).symm

theorem sim_LHU (rd rs1 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Load (.LHU (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LHU (regOfBits rd) (regOfBits rs1) off))
    (hs : MemSafe C ms (.Load (.LHU (rd, rs1, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  have hv : RiscvZkvm.Rv64.isValidHalfwordAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (BitVec.setWidth 64 (holWordExtract 16 15 0
    (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms))) _ ?_
    (by rw [RiscvZkvm.Rv64.step_lhu hc hv]; rfl) ?_
  · simp only [Run, «dfn'LHU», translateAddr, GPR_fetched]; rfl
  · rw [GPR_eq C hR] at hs ⊢
    exact (load_lhu hR.mem _ (aligned2_of_valid hs)).symm

theorem sim_LBU (rd rs1 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Load (.LBU (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LBU (regOfBits rd) (regOfBits rs1) off))
    (hs : MemSafe C ms (.Load (.LBU (rd, rs1, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  have hv : RiscvZkvm.Rv64.isValidByteAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (BitVec.setWidth 64 (holWordExtract 8 7 0
    (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms))) _ ?_
    (by rw [RiscvZkvm.Rv64.step_lbu hc hv]; rfl) ?_
  · simp only [Run, «dfn'LBU», translateAddr, GPR_fetched]; rfl
  · rw [GPR_eq C hR]
    exact (load_lbu hR.mem _).symm

end Loads

/-! ### Stores -/

theorem l3Word_frame {m m' : BitVec 64 → BitVec 8} {a : BitVec 64}
    (h : ∀ i < 4, m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    l3Word m' a = l3Word m a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3
  simp only [l3Word, h0]
  rw [show a + 1 = a + 1#64 from rfl, show a + 2 = a + 2#64 from rfl,
    show a + 3 = a + 3#64 from rfl, h1, h2, h3]

/-- Generic store simulation. -/
theorem sim_store {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
    {i : instruction} (h : AtPc ms i) (p v : BitVec 64) (n : Nat)
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) (hp : p.toNat % n = 0) (hnc : NoCodeWrite C p n)
    (hrun : Run i (fetched ms) = rawWriteData (p, v, n) (fetched ms))
    (m1 : MachineState) (hregs : m1.regs = z.m.regs) (hcode : m1.code = z.m.code)
    (hpc1 : m1.pc = z.m.pc)
    (hmem : MemRel (rawWriteData (p, v, n) (fetched ms)).MEM8 m1.mem)
    (hz : RiscvZkvm.Rv64.step z.m = some (m1.setPC (z.m.pc + 4))) :
    StepsAgree C ms z := by
  have f := (riscvOk_iff ms).mp h.ok
  have hw := rawWriteData_eq (ms := fetched ms) p v n
  refine ⟨_, _, l3_next_normal h _ hrun ?_ ?_, hz, ?_⟩
  · rw [hw]; exact f.2.2.2.1
  · rw [hw]; exact f.2.2.1
  · rw [hw]
    apply rel_post h.ok
    · rfl
    · rfl
    · exact f.2.2.2.1
    · simp [«write'PC», fetched, holUpdate, f.2.2.1]
    · simp [«write'PC», fetched, holUpdate, Skip, hR.pc]
    · intro r; simp [«write'PC», fetched, hregs, hR.regs r]
    · exact hmem
    · intro a ha
      simp only [z_setPC_code, hcode, «write'PC»]
      rw [hR.code a ha]
      congr 1
      symm
      apply l3Word_frame
      intro k hk
      exact store_frame (ms := fetched ms) p v n hn hp _ (fun j hj => hnc a ha k hk j hj)

section Stores
variable {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
include hR

theorem sim_SD (rs1 rs2 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Store (.SD (rs1, rs2, off))))
    (hc : z.m.code z.m.pc = some (.SD (regOfBits rs1) (regOfBits rs2) off))
    (hs : MemSafe C ms (.Store (.SD (rs1, rs2, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  obtain ⟨hs, hnc⟩ := hs
  have hv : RiscvZkvm.Rv64.isValidDwordAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_store hR h _ (GPR rs2 ms) 8 (by omega) (aligned8_of_valid hs) hnc ?_
    (z.m.setMem (GPR rs1 ms + BitVec.signExtend 64 off) (GPR rs2 ms)) rfl rfl rfl
    (store_sd (ms := fetched ms) hR.mem _ _ (aligned8_of_valid hs)) ?_
  · simp only [Run, «dfn'SD», in32_fetched h.ok, translateAddr, GPR_fetched, Bool.false_eq_true,
      if_false]
  · rw [RiscvZkvm.Rv64.step_sd hc hv]
    simp only [RiscvZkvm.Rv64.execInstrBr, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12]

theorem sim_SW (rs1 rs2 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Store (.SW (rs1, rs2, off))))
    (hc : z.m.code z.m.pc = some (.SW (regOfBits rs1) (regOfBits rs2) off))
    (hs : MemSafe C ms (.Store (.SW (rs1, rs2, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  obtain ⟨hs, hnc⟩ := hs
  have hv : RiscvZkvm.Rv64.isValidMemAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_store hR h _ (GPR rs2 ms) 4 (by omega) (aligned4_of_valid hs) hnc ?_
    (z.m.setWord32 (GPR rs1 ms + BitVec.signExtend 64 off) ((GPR rs2 ms).truncate 32)) rfl rfl rfl
    (store_sw (ms := fetched ms) hR.mem _ _ (aligned4_of_valid hs)) ?_
  · simp only [Run, «dfn'SW», translateAddr, GPR_fetched]
  · rw [RiscvZkvm.Rv64.step_sw hc hv]
    simp only [RiscvZkvm.Rv64.execInstrBr, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12]

theorem sim_SH (rs1 rs2 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Store (.SH (rs1, rs2, off))))
    (hc : z.m.code z.m.pc = some (.SH (regOfBits rs1) (regOfBits rs2) off))
    (hs : MemSafe C ms (.Store (.SH (rs1, rs2, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  obtain ⟨hs, hnc⟩ := hs
  have hv : RiscvZkvm.Rv64.isValidHalfwordAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_store hR h _ (GPR rs2 ms) 2 (by omega) (aligned2_of_valid hs) hnc ?_
    (z.m.setHalfword (GPR rs1 ms + BitVec.signExtend 64 off) ((GPR rs2 ms).truncate 16)) rfl rfl
    rfl (store_sh (ms := fetched ms) hR.mem _ _ (aligned2_of_valid hs)) ?_
  · simp only [Run, «dfn'SH», translateAddr, GPR_fetched]
  · rw [RiscvZkvm.Rv64.step_sh hc hv]
    simp only [RiscvZkvm.Rv64.execInstrBr, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12]

theorem sim_SB (rs1 rs2 : BitVec 5) (off : BitVec 12) (h : AtPc ms (.Store (.SB (rs1, rs2, off))))
    (hc : z.m.code z.m.pc = some (.SB (regOfBits rs1) (regOfBits rs2) off))
    (hs : MemSafe C ms (.Store (.SB (rs1, rs2, off)))) :
    StepsAgree C ms z := by
  simp only [MemSafe] at hs
  obtain ⟨hs, hnc⟩ := hs
  have hv : RiscvZkvm.Rv64.isValidByteAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_store hR h _ (GPR rs2 ms) 1 (by omega) (by omega) hnc ?_
    (z.m.setByte (GPR rs1 ms + BitVec.signExtend 64 off) ((GPR rs2 ms).truncate 8)) rfl rfl
    rfl (store_sb (ms := fetched ms) hR.mem _ _) ?_
  · simp only [Run, «dfn'SB», translateAddr, GPR_fetched]
  · rw [RiscvZkvm.Rv64.step_sb hc hv]
    simp only [RiscvZkvm.Rv64.execInstrBr, GPR_eq C hR, RiscvZkvm.Rv64.signExtend12]

end Stores

end RiscvImCompare
