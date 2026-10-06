import RiscvImCompare.ZDecode

/-!
# The two instruction decoders agree on arbitrary words, except on SYSTEM

Compares L3's `Decode : BitVec 32 → instruction` with riscv-zkvm's
`decode : BitVec 32 → Option Instr` on *every* 32-bit word, via `toZx`.

* `decode_eq_toZx`: for every word whose major opcode is not `0x73` (SYSTEM),
  `decode w = toZx (Decode w)`. In particular both reject the same words there (FENCE: both
  accept any fm/pred/succ/rd/rs1 with funct3 = 0; shifts: both require funct6 = 0 / 0x10 and use
  bit 25 as shamt[5]; R-type: both require the exact funct7).
* Direction A (`decode_some_toZx`): if riscv-zkvm decodes `w` to `zi`, then `zi` is `ECALL`,
  `EBREAK` or `CSRS`, or `toZx (Decode w) = some zi`.
* Direction B (`Decode_toZx`): if L3 decodes `w` to something other than
  `UnknownInstruction`, `ECALL` or `EBREAK`, then `decode w = toZx (Decode w)`.
* The only disagreements are on SYSTEM words (`Decode_system`, `decode_ecall_L3`,
  `decode_ebreak_L3`, `decode_csrs_L3`): L3 decodes only `0x00000073` (ECALL) and `0x00100073`
  (EBREAK); riscv-zkvm also decodes ECALL/EBREAK with arbitrary rd/rs1 fields
  (1023 extra words each, e.g. `0x000000f3`, `0x00108073`) and CSRRS with rd = x0 as `CSRS`
  (2^17 words, e.g. `0x00002073`), all of which L3 rejects.

The proof splits on the opcode bits: one lemma `op_XX` per opcode, each simplifying L3's decision
tree under the fixed opcode bits and then splitting on funct3 / funct7 bits where needed.
-/

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


macro "prune" : tactic => `(tactic| simp only [Bool.true_and, Bool.false_and, Bool.and_true,
  Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, ite_self, *])

macro "zred" : tactic => `(tactic| simp only [decode, toNat7, toNat3, toNat6,
  BitVec.getLsbD_extractLsb', Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.zero_add, decide_true,
  Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false,
  Bool.false_eq_true, ite_true, ite_false, ite_self, Bool.toNat_true, Bool.toNat_false, toZx, toZ,
  f_br0, f_jal0, beq_self_eq_true, Nat.reduceBEq, *])

macro "fields" : tactic => `(tactic| simp only [Decode, boolify32, f_rd, f_rs1, f_rs2, f_immI,
  f_immU, f_sh, f_br, f_st, f_jal])
set_option maxHeartbeats 4000000 in
theorem op_03 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_07 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_0b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_0f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_13 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)
  all_goals (cases h25 : w.getLsbD 25 <;> cases h26 : w.getLsbD 26 <;> cases h27 : w.getLsbD 27 <;>
    cases h28 : w.getLsbD 28 <;> cases h29 : w.getLsbD 29 <;> cases h30 : w.getLsbD 30 <;>
    cases h31 : w.getLsbD 31 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_17 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_1b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_1f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_23 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_27 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_2b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_2f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_33 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)
  all_goals (cases h25 : w.getLsbD 25 <;> cases h26 : w.getLsbD 26 <;> cases h27 : w.getLsbD 27 <;>
    cases h28 : w.getLsbD 28 <;> cases h29 : w.getLsbD 29 <;> cases h30 : w.getLsbD 30 <;>
    cases h31 : w.getLsbD 31 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_37 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_3b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_3f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = false) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_43 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_47 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_4b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_4f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_53 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_57 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_5b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_5f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = false) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_63 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_67 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred
  all_goals (cases h12 : w.getLsbD 12 <;> cases h13 : w.getLsbD 13 <;> cases h14 : w.getLsbD 14 <;> prune <;> zred)

set_option maxHeartbeats 4000000 in
theorem op_6b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_6f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = false) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_77 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_7b (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_7f (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true) (b2 : w.getLsbD 2 = true) (b3 : w.getLsbD 3 = true) (b4 : w.getLsbD 4 = true) (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    toZx (Decode w) = decode w := by
  fields
  prune
  zred

set_option maxHeartbeats 4000000 in
theorem op_low00 (w : BitVec 32) (b0 : w.getLsbD 0 = false) (b1 : w.getLsbD 1 = false) :
    toZx (Decode w) = decode w := by
  simp only [Decode, boolify32]
  prune
  cases b2 : w.getLsbD 2 <;> cases b3 : w.getLsbD 3 <;> cases b4 : w.getLsbD 4 <;>
    cases b5 : w.getLsbD 5 <;> cases b6 : w.getLsbD 6 <;> zred

set_option maxHeartbeats 4000000 in
theorem op_low01 (w : BitVec 32) (b0 : w.getLsbD 0 = false) (b1 : w.getLsbD 1 = true) :
    toZx (Decode w) = decode w := by
  simp only [Decode, boolify32]
  prune
  cases b2 : w.getLsbD 2 <;> cases b3 : w.getLsbD 3 <;> cases b4 : w.getLsbD 4 <;>
    cases b5 : w.getLsbD 5 <;> cases b6 : w.getLsbD 6 <;> zred

set_option maxHeartbeats 4000000 in
theorem op_low10 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = false) :
    toZx (Decode w) = decode w := by
  simp only [Decode, boolify32]
  prune
  cases b2 : w.getLsbD 2 <;> cases b3 : w.getLsbD 3 <;> cases b4 : w.getLsbD 4 <;>
    cases b5 : w.getLsbD 5 <;> cases b6 : w.getLsbD 6 <;> zred

theorem opc_of_bits (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true)
    (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true)
    (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) : w.extractLsb' 0 7 = 0x73#7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, *] <;> decide

/-- **Agreement outside the SYSTEM opcode.** For every 32-bit word whose major opcode is not
`0x73` (SYSTEM), riscv-zkvm's decoder returns exactly the `toZx`-image of L3's decoding (both
`none`/`UnknownInstruction` on the words neither supports). -/
theorem decode_eq_toZx (w : BitVec 32) (h : w.extractLsb' 0 7 ≠ 0x73#7) :
    decode w = toZx (Decode w) := by
  symm
  cases b0 : w.getLsbD 0 <;> cases b1 : w.getLsbD 1 <;> cases b2 : w.getLsbD 2 <;>
    cases b3 : w.getLsbD 3 <;> cases b4 : w.getLsbD 4 <;> cases b5 : w.getLsbD 5 <;>
    cases b6 : w.getLsbD 6
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low00 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low01 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_low10 w b0 b1
  · exact op_03 w b0 b1 b2 b3 b4 b5 b6
  · exact op_43 w b0 b1 b2 b3 b4 b5 b6
  · exact op_23 w b0 b1 b2 b3 b4 b5 b6
  · exact op_63 w b0 b1 b2 b3 b4 b5 b6
  · exact op_13 w b0 b1 b2 b3 b4 b5 b6
  · exact op_53 w b0 b1 b2 b3 b4 b5 b6
  · exact op_33 w b0 b1 b2 b3 b4 b5 b6
  · exact absurd (opc_of_bits w b0 b1 b2 b3 b4 b5 b6) h
  · exact op_0b w b0 b1 b2 b3 b4 b5 b6
  · exact op_4b w b0 b1 b2 b3 b4 b5 b6
  · exact op_2b w b0 b1 b2 b3 b4 b5 b6
  · exact op_6b w b0 b1 b2 b3 b4 b5 b6
  · exact op_1b w b0 b1 b2 b3 b4 b5 b6
  · exact op_5b w b0 b1 b2 b3 b4 b5 b6
  · exact op_3b w b0 b1 b2 b3 b4 b5 b6
  · exact op_7b w b0 b1 b2 b3 b4 b5 b6
  · exact op_07 w b0 b1 b2 b3 b4 b5 b6
  · exact op_47 w b0 b1 b2 b3 b4 b5 b6
  · exact op_27 w b0 b1 b2 b3 b4 b5 b6
  · exact op_67 w b0 b1 b2 b3 b4 b5 b6
  · exact op_17 w b0 b1 b2 b3 b4 b5 b6
  · exact op_57 w b0 b1 b2 b3 b4 b5 b6
  · exact op_37 w b0 b1 b2 b3 b4 b5 b6
  · exact op_77 w b0 b1 b2 b3 b4 b5 b6
  · exact op_0f w b0 b1 b2 b3 b4 b5 b6
  · exact op_4f w b0 b1 b2 b3 b4 b5 b6
  · exact op_2f w b0 b1 b2 b3 b4 b5 b6
  · exact op_6f w b0 b1 b2 b3 b4 b5 b6
  · exact op_1f w b0 b1 b2 b3 b4 b5 b6
  · exact op_5f w b0 b1 b2 b3 b4 b5 b6
  · exact op_3f w b0 b1 b2 b3 b4 b5 b6
  · exact op_7f w b0 b1 b2 b3 b4 b5 b6

/-! ## The SYSTEM opcode (`0x73`) -/

/-- L3 decodes exactly two SYSTEM words, the canonical `ecall` (`0x00000073`) and `ebreak`
(`0x00100073`); every other SYSTEM word (including all CSR instructions) is unknown to it. -/
theorem op_73 (w : BitVec 32) (b0 : w.getLsbD 0 = true) (b1 : w.getLsbD 1 = true)
    (b2 : w.getLsbD 2 = false) (b3 : w.getLsbD 3 = false) (b4 : w.getLsbD 4 = true)
    (b5 : w.getLsbD 5 = true) (b6 : w.getLsbD 6 = true) :
    Decode w = if w = 0x00000073#32 then .System .ECALL
      else if w = 0x00100073#32 then .System .EBREAK else .UnknownInstruction := by
  by_cases hw : w = 0x00000073#32
  · subst hw; rfl
  by_cases hw2 : w = 0x00100073#32
  · subst hw2; rfl
  rw [if_neg hw, if_neg hw2]
  simp only [Decode, boolify32]
  prune
  split_ifs <;> first
    | rfl
    | (exfalso
       simp only [Bool.and_eq_true, Bool.not_eq_true'] at *
       first
         | (apply hw; apply BitVec.eq_of_getLsbD_eq; intro i hi
            interval_cases i <;> simp only [*] <;> decide)
         | (apply hw2; apply BitVec.eq_of_getLsbD_eq; intro i hi
            interval_cases i <;> simp only [*] <;> decide))

theorem bit_of_eq {w : BitVec 32} {s n : Nat} {v : BitVec n} (h : w.extractLsb' s n = v) (i : Nat)
    (hi : i < n) : w.getLsbD (s + i) = v.getLsbD i := by
  rw [← h]; simp [hi]

theorem bits_of_opc {w : BitVec 32} (h : w.extractLsb' 0 7 = 0x73#7) :
    w.getLsbD 0 = true ∧ w.getLsbD 1 = true ∧ w.getLsbD 2 = false ∧ w.getLsbD 3 = false ∧
      w.getLsbD 4 = true ∧ w.getLsbD 5 = true ∧ w.getLsbD 6 = true :=
  ⟨(bit_of_eq h 0 (by omega)).trans (by decide), (bit_of_eq h 1 (by omega)).trans (by decide),
    (bit_of_eq h 2 (by omega)).trans (by decide), (bit_of_eq h 3 (by omega)).trans (by decide),
    (bit_of_eq h 4 (by omega)).trans (by decide), (bit_of_eq h 5 (by omega)).trans (by decide),
    (bit_of_eq h 6 (by omega)).trans (by decide)⟩

theorem Decode_system (w : BitVec 32) (h : w.extractLsb' 0 7 = 0x73#7) :
    Decode w = if w = 0x00000073#32 then .System .ECALL
      else if w = 0x00100073#32 then .System .EBREAK else .UnknownInstruction := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := bits_of_opc h
  exact op_73 w b0 b1 b2 b3 b4 b5 b6

/-! ## Direction A: riscv-zkvm → L3 -/

/-- Every word riscv-zkvm decodes, other than to `ECALL`, `EBREAK` or a `CSRS`, is decoded by L3
to an instruction that `toZx` maps to the same riscv-zkvm instruction. -/
theorem decode_some_toZx (w : BitVec 32) (zi : Instr) (hz : decode w = some zi) :
    zi = .ECALL ∨ zi = .EBREAK ∨ (∃ c r, zi = .CSRS c r) ∨ toZx (Decode w) = some zi := by
  by_cases h : w.extractLsb' 0 7 = 0x73#7
  · have h115 : (w.extractLsb' 0 7).toNat = 115 := by rw [h]; rfl
    simp only [decode, h115] at hz
    revert hz
    split_ifs <;> (try split) <;> intro hz <;> cases hz <;> simp
  · exact Or.inr (Or.inr (Or.inr (by rw [← decode_eq_toZx w h, hz])))

/-! ## Direction B: L3 → riscv-zkvm -/

/-- Every word L3 decodes, other than to `ECALL`/`EBREAK`, is decoded by riscv-zkvm to the
`toZx`-image of L3's instruction. -/
theorem Decode_toZx (w : BitVec 32) (h : Decode w ≠ .UnknownInstruction) :
    Decode w = .System .ECALL ∨ Decode w = .System .EBREAK ∨ decode w = toZx (Decode w) := by
  by_cases hop : w.extractLsb' 0 7 = 0x73#7
  · rw [Decode_system w hop] at h ⊢
    split_ifs at h ⊢ <;> simp_all
  · exact Or.inr (Or.inr (decode_eq_toZx w hop))

/-! ## Exactly where the decoders disagree -/

theorem toZx_ne_system (i : instruction) :
    toZx i ≠ some .ECALL ∧ toZx i ≠ some .EBREAK ∧ ∀ c r, toZx i ≠ some (.CSRS c r) := by
  unfold toZx
  split <;> (try unfold toZ) <;> (try split) <;> simp

theorem opc_of_decode_system {w : BitVec 32} {zi : Instr} (hz : decode w = some zi)
    (hs : zi = .ECALL ∨ zi = .EBREAK ∨ ∃ c r, zi = .CSRS c r) : w.extractLsb' 0 7 = 0x73#7 := by
  by_contra h
  rw [decode_eq_toZx w h] at hz
  obtain ⟨h1, h2, h3⟩ := toZx_ne_system (Decode w)
  rcases hs with rfl | rfl | ⟨c, r, rfl⟩
  · exact h1 hz
  · exact h2 hz
  · exact h3 c r hz

/-- riscv-zkvm decodes `ECALL` from every SYSTEM word with funct3 = 0 and imm = 0, ignoring the
`rd` and `rs1` fields; L3 decodes only the canonical word `0x00000073` (rd = rs1 = x0) and
rejects the other 1023 such words. -/
theorem decode_ecall_L3 (w : BitVec 32) (hz : decode w = some .ECALL) :
    Decode w = if w = 0x00000073#32 then .System .ECALL else .UnknownInstruction := by
  rw [Decode_system w (opc_of_decode_system hz (Or.inl rfl))]
  have : w ≠ 0x00100073#32 := by rintro rfl; exact absurd hz (by decide)
  simp only [this, if_false]

/-- Same for `EBREAK`: riscv-zkvm ignores `rd`/`rs1`; L3 accepts only `0x00100073`. -/
theorem decode_ebreak_L3 (w : BitVec 32) (hz : decode w = some .EBREAK) :
    Decode w = if w = 0x00100073#32 then .System .EBREAK else .UnknownInstruction := by
  rw [Decode_system w (opc_of_decode_system hz (Or.inr (Or.inl rfl)))]
  have : w ≠ 0x00000073#32 := by rintro rfl; exact absurd hz (by decide)
  simp only [this, if_false]

/-- riscv-zkvm's `CSRS` (CSRRS with rd = x0, the ZisK accelerator call) is unknown to L3. -/
theorem decode_csrs_L3 (w : BitVec 32) (c : BitVec 12) (r : RiscvZkvm.Rv64.Reg)
    (hz : decode w = some (.CSRS c r)) : Decode w = .UnknownInstruction := by
  rw [Decode_system w (opc_of_decode_system hz (Or.inr (Or.inr ⟨c, r, rfl⟩)))]
  have h1 : w ≠ 0x00000073#32 := by
    rintro rfl; rw [show decode 0x00000073#32 = some .ECALL by decide] at hz; simp at hz
  have h2 : w ≠ 0x00100073#32 := by
    rintro rfl; rw [show decode 0x00100073#32 = some .EBREAK by decide] at hz; simp at hz
  simp only [h1, h2, if_false]

/-- Concrete witnesses: `ecall` with rd = x1 (`0x000000f3`), `ebreak` with rs1 = x1
(`0x00108073`), and `csrs 0x000, x0` (`0x00002073`). -/
example : decode 0x000000f3#32 = some .ECALL ∧ Decode 0x000000f3#32 = .UnknownInstruction := by
  constructor <;> rfl
example : decode 0x00108073#32 = some .EBREAK ∧ Decode 0x00108073#32 = .UnknownInstruction := by
  constructor <;> rfl
example : decode 0x00002073#32 = some (.CSRS 0#12 .x0) ∧
    Decode 0x00002073#32 = .UnknownInstruction := by
  constructor <;> rfl

/-- On SYSTEM words, L3's `ECALL`/`EBREAK` are also riscv-zkvm's. -/
theorem Decode_system_agree (w : BitVec 32) (hop : w.extractLsb' 0 7 = 0x73#7)
    (h : Decode w = .System .ECALL ∨ Decode w = .System .EBREAK) :
    (Decode w = .System .ECALL ∧ decode w = some .ECALL) ∨
      (Decode w = .System .EBREAK ∧ decode w = some .EBREAK) := by
  rw [Decode_system w hop] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · subst h1; exact Or.inl ⟨rfl, by decide⟩
  · subst h2; exact Or.inr ⟨rfl, by decide⟩
  · simp at h

end RiscvImCompare
