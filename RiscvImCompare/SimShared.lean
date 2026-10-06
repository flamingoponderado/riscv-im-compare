import RiscvImCompare.SimStep

/-!
# Step simulation for the shared instructions that flapjack never emits

`SLT SLTI SLTIU ADDIW LB LH LW MULH MULHSU DIVU REM REMU FENCE` are implemented
by both L3 and riscv-zkvm. These lemmas prove that, whenever L3 executes one of
them (fetched from an arbitrary word) and riscv-zkvm's code map holds the
corresponding instruction, the two steps agree.
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

theorem signExtend_self (x : BitVec 64) : BitVec.signExtend 64 x = x := by
  simp

theorem mulh_eq (a b : BitVec 64) :
    holWordExtract 64 127 64 (BitVec.signExtend 128 a * BitVec.signExtend 128 b) =
      RiscvZkvm.Rv64.rv64_mulh a b := by
  rw [holWordExtract_eq_extractLsb' _ 64 127 64 (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp [RiscvZkvm.Rv64.rv64_mulh, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem mulhsu_eq (a b : BitVec 64) :
    holWordExtract 64 127 64 (BitVec.signExtend 128 a * BitVec.setWidth 128 b) =
      RiscvZkvm.Rv64.rv64_mulhsu a b := by
  rw [holWordExtract_eq_extractLsb' _ 64 127 64 (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp [RiscvZkvm.Rv64.rv64_mulhsu, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem addiw_eq (a : BitVec 64) (imm : BitVec 12) :
    BitVec.signExtend 64 (holWordExtract 32 31 0 (a + BitVec.signExtend 64 imm)) =
      ((a.truncate 32 + (RiscvZkvm.Rv64.signExtend12 imm).truncate 32 : BitVec 32)).signExtend 64 := by
  rw [holWordExtract_eq_extractLsb' _ 32 31 0 (by omega) (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [RiscvZkvm.Rv64.signExtend12, BitVec.extractLsb'_toNat, BitVec.toNat_add]

section Shared
variable {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
include hR

theorem sim_SLT (rd rs1 rs2 : BitVec 5) {w : BitVec 32} (h : AtPcW ms w (.ArithR (.SLT (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.SLT (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (holV2w 64 [BitVec.slt (GPR rs1 ms) (GPR rs2 ms)]) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'SLT», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [holV2w_bool]; simp [GPR_eq C hR]

theorem sim_SLTI (rd rs1 : BitVec 5) (imm : BitVec 12) {w : BitVec 32}
    (h : AtPcW ms w (.ArithI (.SLTI (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.SLTI (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (holV2w 64 [BitVec.slt (GPR rs1 ms) (BitVec.signExtend 64 imm)]) _ ?_
    (by zstep) ?_
  · simp only [Run, «dfn'SLTI», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [holV2w_bool]; simp only [GPR_eq C hR, RiscvZkvm.Rv64.signExtend12]
    split <;> simp_all

theorem sim_SLTIU (rd rs1 : BitVec 5) (imm : BitVec 12) {w : BitVec 32}
    (h : AtPcW ms w (.ArithI (.SLTIU (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.SLTIU (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (holV2w 64 [BitVec.ult (GPR rs1 ms) (BitVec.signExtend 64 imm)]) _ ?_
    (by zstep) ?_
  · simp only [Run, «dfn'SLTIU», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [holV2w_bool]; simp only [GPR_eq C hR, RiscvZkvm.Rv64.signExtend12]
    split <;> simp_all

theorem sim_ADDIW (rd rs1 : BitVec 5) (imm : BitVec 12) {w : BitVec 32}
    (h : AtPcW ms w (.ArithI (.ADDIW (rd, rs1, imm))))
    (hc : z.m.code z.m.pc = some (.ADDIW (regOfBits rd) (regOfBits rs1) imm)) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (BitVec.signExtend 64 (holWordExtract 32 31 0 (GPR rs1 ms + BitVec.signExtend 64 imm))) _ ?_
    (by zstep) ?_
  · simp only [Run, «dfn'ADDIW», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [addiw_eq, GPR_eq C hR]

theorem sim_MULH (rd rs1 rs2 : BitVec 5) {w : BitVec 32}
    (h : AtPcW ms w (.MulDiv (.MULH (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.MULH (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (BitVec.signExtend 64 (holWordExtract 64 127 64
    (BitVec.signExtend 128 (GPR rs1 ms) * BitVec.signExtend 128 (GPR rs2 ms)))) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'MULH», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [signExtend_self, mulh_eq]; simp only [GPR_eq C hR]

theorem sim_MULHSU (rd rs1 rs2 : BitVec 5) {w : BitVec 32}
    (h : AtPcW ms w (.MulDiv (.MULHSU (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.MULHSU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd (holWordExtract 64 127 64
    (BitVec.signExtend 128 (GPR rs1 ms) * BitVec.setWidth 128 (GPR rs2 ms))) _ ?_ (by zstep) ?_
  · simp only [Run, «dfn'MULHSU», in32_fetched h.ok, GPR_fetched, Bool.false_eq_true, if_false]
  · rw [mulhsu_eq]; simp only [GPR_eq C hR]

theorem sim_DIVU (rd rs1 rs2 : BitVec 5) {w : BitVec 32}
    (h : AtPcW ms w (.MulDiv (.DIVU (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.DIVU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (if (GPR rs2 ms == BitVec.ofNat 64 0) = true then BitVec.signExtend 64 (BitVec.ofNat 1 1)
      else BitVec.udiv (GPR rs1 ms) (GPR rs2 ms)) _ ?_ (by zstep) ?_
  · by_cases hb : (GPR rs2 ms == BitVec.ofNat 64 0) = true <;>
      simp [Run, «dfn'DIVU», in32_fetched h.ok, GPR_fetched, hb]
  · simp only [RiscvZkvm.Rv64.rv64_divu, GPR_eq C hR]
    have : BitVec.signExtend 64 (BitVec.ofNat 1 1) = BitVec.allOnes 64 := by decide
    rw [this]; rfl

theorem sim_REM (rd rs1 rs2 : BitVec 5) {w : BitVec 32}
    (h : AtPcW ms w (.MulDiv (.REM (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.REM (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (if (GPR rs2 ms == BitVec.ofNat 64 0) = true then GPR rs1 ms
      else BitVec.srem (GPR rs1 ms) (GPR rs2 ms)) _ ?_ (by zstep) ?_
  · by_cases hb : (GPR rs2 ms == BitVec.ofNat 64 0) = true <;>
      simp [Run, «dfn'REM», GPR_fetched, hb]
  · simp only [RiscvZkvm.Rv64.rv64_rem, GPR_eq C hR]

theorem sim_REMU (rd rs1 rs2 : BitVec 5) {w : BitVec 32}
    (h : AtPcW ms w (.MulDiv (.REMU (rd, rs1, rs2))))
    (hc : z.m.code z.m.pc = some (.REMU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))) :
    StepsAgree C ms z := by
  refine sim_write' hR h rd
    (if (GPR rs2 ms == BitVec.ofNat 64 0) = true then GPR rs1 ms
      else BitVec.umod (GPR rs1 ms) (GPR rs2 ms)) _ ?_ (by zstep) ?_
  · by_cases hb : (GPR rs2 ms == BitVec.ofNat 64 0) = true <;>
      simp [Run, «dfn'REMU», GPR_fetched, hb]
  · simp only [RiscvZkvm.Rv64.rv64_remu, GPR_eq C hR]; rfl

theorem sim_FENCE (p : BitVec 5 × BitVec 5 × BitVec 4 × BitVec 4) {w : BitVec 32}
    (h : AtPcW ms w (.FENCE p))
    (hc : z.m.code z.m.pc = some .FENCE) :
    StepsAgree C ms z := by
  refine sim_write' hR h 0 0 0 ?_ (by zstep) rfl
  simp [Run, «write'GPR»]

end Shared

theorem narrow_of_zext {n : Nat} (hn : n ≤ 64) (a b : BitVec n)
    (h : a.zeroExtend 64 = b.setWidth 64) : a = b := by
  have := congrArg (BitVec.setWidth n) h
  simpa [BitVec.setWidth_setWidth_of_le _ hn] using this

section SignedLoads
variable {C : BitVec 64 → Prop} {ms : riscv_state} {z : ZState} (hR : Rel C ms z)
include hR

theorem sim_LW (rd rs1 : BitVec 5) (off : BitVec 12) {w : BitVec 32}
    (h : AtPcW ms w (.Load (.LW (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LW (regOfBits rd) (regOfBits rs1) off))
    (hs : RiscvZkvm.Rv64.isValidMemAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true) :
    StepsAgree C ms z := by
  have hv : RiscvZkvm.Rv64.isValidMemAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (BitVec.signExtend 64 (holWordExtract 32 31 0
    (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms))) _ ?_
    (by rw [RiscvZkvm.Rv64.step_lw hc hv]; rfl) ?_
  · simp only [Run, «dfn'LW», translateAddr, GPR_fetched]; rfl
  · rw [GPR_eq C hR] at hs ⊢
    simp only [RiscvZkvm.Rv64.signExtend12]
    rw [narrow_of_zext (by omega) _ _ (load_lwu hR.mem _ (aligned4_of_valid hs))]

theorem sim_LH (rd rs1 : BitVec 5) (off : BitVec 12) {w : BitVec 32}
    (h : AtPcW ms w (.Load (.LH (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LH (regOfBits rd) (regOfBits rs1) off))
    (hs : RiscvZkvm.Rv64.isValidHalfwordAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true) :
    StepsAgree C ms z := by
  have hv : RiscvZkvm.Rv64.isValidHalfwordAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (BitVec.signExtend 64 (holWordExtract 16 15 0
    (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms))) _ ?_
    (by rw [RiscvZkvm.Rv64.step_lh hc hv]; rfl) ?_
  · simp only [Run, «dfn'LH», translateAddr, GPR_fetched]; rfl
  · rw [GPR_eq C hR] at hs ⊢
    simp only [RiscvZkvm.Rv64.signExtend12]
    rw [narrow_of_zext (by omega) _ _ (load_lhu hR.mem _ (aligned2_of_valid hs))]

theorem sim_LB (rd rs1 : BitVec 5) (off : BitVec 12) {w : BitVec 32}
    (h : AtPcW ms w (.Load (.LB (rd, rs1, off))))
    (hc : z.m.code z.m.pc = some (.LB (regOfBits rd) (regOfBits rs1) off))
    (hs : RiscvZkvm.Rv64.isValidByteAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true) :
    StepsAgree C ms z := by
  have hv : RiscvZkvm.Rv64.isValidByteAccess
      (z.m.getReg (regOfBits rs1) + RiscvZkvm.Rv64.signExtend12 off) = true := by
    rw [← GPR_eq C hR]; exact hs
  refine sim_write' hR h rd (BitVec.signExtend 64 (holWordExtract 8 7 0
    (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms))) _ ?_
    (by rw [RiscvZkvm.Rv64.step_lb hc hv]; rfl) ?_
  · simp only [Run, «dfn'LB», translateAddr, GPR_fetched]; rfl
  · rw [GPR_eq C hR]
    simp only [RiscvZkvm.Rv64.signExtend12]
    rw [narrow_of_zext (by omega) _ _ (load_lbu hR.mem _)]

end SignedLoads

end RiscvImCompare
