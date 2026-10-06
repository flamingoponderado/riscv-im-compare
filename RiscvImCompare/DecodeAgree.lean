import RiscvImCompare.ZDecode

namespace RiscvImCompare

open Flapjack.RiscV.L3
open RiscvZkvm.Rv64 (Instr)
open RiscvZkvm.Interpreter

set_option maxRecDepth 200000

section Fields
variable (w : BitVec 32)

macro "fbits_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [holV2w, Flapjack.getLsbD_holFcpWord, immI, immS, immB, immU, immJ, asImm12, asSImm12,
    asImm20, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  interval_cases j <;> simp))

theorem f_rd : holV2w 5 [w.getLsbD 11, w.getLsbD 10, w.getLsbD 9, w.getLsbD 8, w.getLsbD 7] =
    w.extractLsb' 7 5 := by fbits_tac
theorem f_rs1 : holV2w 5 [w.getLsbD 19, w.getLsbD 18, w.getLsbD 17, w.getLsbD 16, w.getLsbD 15] =
    w.extractLsb' 15 5 := by fbits_tac
theorem f_rs2 : holV2w 5 [w.getLsbD 24, w.getLsbD 23, w.getLsbD 22, w.getLsbD 21, w.getLsbD 20] =
    w.extractLsb' 20 5 := by fbits_tac
theorem f_immI : holV2w 12 [w.getLsbD 31, w.getLsbD 30, w.getLsbD 29, w.getLsbD 28, w.getLsbD 27,
    w.getLsbD 26, w.getLsbD 25, w.getLsbD 24, w.getLsbD 23, w.getLsbD 22, w.getLsbD 21,
    w.getLsbD 20] = immI w := by fbits_tac
theorem f_immU : holV2w 20 [w.getLsbD 31, w.getLsbD 30, w.getLsbD 29, w.getLsbD 28, w.getLsbD 27,
    w.getLsbD 26, w.getLsbD 25, w.getLsbD 24, w.getLsbD 23, w.getLsbD 22, w.getLsbD 21,
    w.getLsbD 20, w.getLsbD 19, w.getLsbD 18, w.getLsbD 17, w.getLsbD 16, w.getLsbD 15,
    w.getLsbD 14, w.getLsbD 13, w.getLsbD 12] = immU w := by fbits_tac
theorem f_sh : holV2w 6 [w.getLsbD 25, w.getLsbD 24, w.getLsbD 23, w.getLsbD 22, w.getLsbD 21,
    w.getLsbD 20] = w.extractLsb' 20 6 := by fbits_tac
theorem f_br : asImm12 (holV2w 1 [w.getLsbD 31], holV2w 1 [w.getLsbD 7],
    holV2w 6 [w.getLsbD 30, w.getLsbD 29, w.getLsbD 28, w.getLsbD 27, w.getLsbD 26, w.getLsbD 25],
    holV2w 4 [w.getLsbD 11, w.getLsbD 10, w.getLsbD 9, w.getLsbD 8]) =
    (immB w).extractLsb' 1 12 := by fbits_tac
theorem f_st : asSImm12 (holV2w 7 [w.getLsbD 31, w.getLsbD 30, w.getLsbD 29, w.getLsbD 28,
    w.getLsbD 27, w.getLsbD 26, w.getLsbD 25], w.extractLsb' 7 5) = immS w := by fbits_tac
theorem f_jal : asImm20 (holV2w 1 [w.getLsbD 31],
    holV2w 8 [w.getLsbD 19, w.getLsbD 18, w.getLsbD 17, w.getLsbD 16, w.getLsbD 15, w.getLsbD 14,
      w.getLsbD 13, w.getLsbD 12], holV2w 1 [w.getLsbD 20],
    holV2w 10 [w.getLsbD 30, w.getLsbD 29, w.getLsbD 28, w.getLsbD 27, w.getLsbD 26, w.getLsbD 25,
      w.getLsbD 24, w.getLsbD 23, w.getLsbD 22, w.getLsbD 21]) =
    (immJ w).extractLsb' 1 20 := by fbits_tac
theorem f_br0 : (immB w).extractLsb' 1 12 ++ 0#1 = immB w := by fbits_tac
theorem f_jal0 : (immJ w).extractLsb' 1 20 ++ 0#1 = immJ w := by fbits_tac

end Fields

theorem toNat3 (x : BitVec 3) :
    x.toNat = (x.getLsbD 0).toNat + 2 * (x.getLsbD 1).toNat + 4 * (x.getLsbD 2).toNat := by
  revert x; decide
theorem toNat6 (x : BitVec 6) :
    x.toNat = (x.getLsbD 0).toNat + 2 * (x.getLsbD 1).toNat + 4 * (x.getLsbD 2).toNat +
      8 * (x.getLsbD 3).toNat + 16 * (x.getLsbD 4).toNat + 32 * (x.getLsbD 5).toNat := by
  revert x; decide
theorem toNat7 (x : BitVec 7) :
    x.toNat = (x.getLsbD 0).toNat + 2 * (x.getLsbD 1).toNat + 4 * (x.getLsbD 2).toNat +
      8 * (x.getLsbD 3).toNat + 16 * (x.getLsbD 4).toNat + 32 * (x.getLsbD 5).toNat +
      64 * (x.getLsbD 6).toNat := by
  revert x; decide

example (w : BitVec 32) (h : w.extractLsb' 0 7 ≠ 0x73#7) : decode w = toZx (Decode w) := by
  have h' : (w.extractLsb' 0 7).toNat ≠ 0x73 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  simp only [Decode, boolify32, f_rd, f_rs1, f_rs2, f_immI, f_immU, f_sh, f_br, f_st, f_jal]
  simp only [decode, toNat3, toNat6, toNat7, BitVec.getLsbD_extractLsb'] at h' ⊢
  simp only [Nat.reduceAdd, Nat.lt_irrefl, decide_true, decide_false, Nat.ofNat_pos, Bool.true_and] at h' ⊢
  trace_state
  sorry
end RiscvImCompare
