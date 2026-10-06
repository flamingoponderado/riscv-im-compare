import RiscvImCompare.Defs
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Backend.Semantics.TargetSem.EncodedBytes
import Mathlib.Tactic.IntervalCases

/-!
# The image of flapjack's RISC-V encoder

Every machine instruction produced by flapjack's RISC-V encoder (`riscvAst`, for
*any* `asm` instruction, not only those the compiler emits) is one of the 37
instructions handled by `toZ`.
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target

theorem riscvAst_supported (a : Flapjack.Compiler.Encoders.Asm.HolAsm 64) :
    ∀ i ∈ riscvAst a, toZ i ≠ none := by
  intro i hi
  unfold riscvAst at hi
  repeat' (split at hi)
  all_goals (try simp only [riscvConst32, riscvEncodeFail, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, or_assoc] at hi)
  all_goals (repeat' (split at hi))
  all_goals (try simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_assoc] at hi)
  all_goals (repeat' (first | (rcases hi with rfl | hi) | (subst hi)))
  all_goals try (simp [toZ]; done)
  all_goals try (rename_i b _ _ _; cases b <;> simp [toZ, riscvBopR]; done)
  all_goals (rename_i m _ _ _ _ _ _
             cases m <;> simp only [riscvMemop, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at * <;>
             subst_vars <;> simp [toZ])

theorem holWordExtract_eq_extractLsb' {a : Nat} (w : BitVec a) (b h l : Nat)
    (hb : h + 1 = l + b) (ha : h < a) : holWordExtract b h l w = w.extractLsb' l b := by
  apply BitVec.eq_of_toNat_eq
  have hmin : min h (a - 1) = h := by omega
  have hw := w.isLt
  simp only [holWordExtract, hmin, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show h + 1 - l = b by omega]
  have hlt : w.toNat / 2 ^ l % 2 ^ b < 2 ^ a := by
    calc w.toNat / 2 ^ l % 2 ^ b ≤ w.toNat / 2 ^ l := Nat.mod_le _ _
      _ ≤ w.toNat := Nat.div_le_self _ _
      _ < 2 ^ a := hw
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_mod]

theorem l3Word_bytes (w : BitVec 32) :
    holWordExtract 8 31 24 w ++ holWordExtract 8 23 16 w ++ holWordExtract 8 15 8 w ++
      holWordExtract 8 7 0 w = w := by
  rw [holWordExtract_eq_extractLsb' w 8 31 24 (by omega) (by omega),
    holWordExtract_eq_extractLsb' w 8 23 16 (by omega) (by omega),
    holWordExtract_eq_extractLsb' w 8 15 8 (by omega) (by omega),
    holWordExtract_eq_extractLsb' w 8 7 0 (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases j <;> simp

theorem l3Word_bytes' (w : BitVec 32) :
    holWordExtract 8 31 24 w ++ (holWordExtract 8 23 16 w ++ (holWordExtract 8 15 8 w ++
      holWordExtract 8 7 0 w)) = w := by
  rw [holWordExtract_eq_extractLsb' w 8 31 24 (by omega) (by omega),
    holWordExtract_eq_extractLsb' w 8 23 16 (by omega) (by omega),
    holWordExtract_eq_extractLsb' w 8 15 8 (by omega) (by omega),
    holWordExtract_eq_extractLsb' w 8 7 0 (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases j <;> simp

theorem riscvEncode_length (i : instruction) : (riscvEncode i).length = 4 := rfl

theorem length_flatMap_riscvEncode (l : List instruction) :
    (l.flatMap riscvEncode).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, riscvEncode_length, ih]; omega

theorem drop_flatMap_riscvEncode (l : List instruction) (k : Nat) :
    (l.flatMap riscvEncode).drop (4 * k) = (l.drop k).flatMap riscvEncode := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.flatMap_cons, show 4 * (k + 1) = 4 + 4 * k by omega, ← List.drop_drop,
        List.drop_left' (riscvEncode_length a), ih]
      simp

/-- **Instruction fetch inside flapjack's machine semantics.** Whenever the
target evaluator executes a step (`encodedBytesInMemHOL` holds at the PC), the
four bytes at the PC are the encoding of a supported instruction and lie in the
domain. -/
theorem encodedBytes_supported (pc : BitVec 64) (m : BitVec 64 → BitVec 8)
    (dom : BitVec 64 → Prop)
    (h : encodedBytesInMemHOL riscvConfig pc m dom) :
    ∃ i, toZ i ≠ none ∧ l3Word m pc = Encode i ∧
      m pc = holWordExtract 8 7 0 (Encode i) ∧
      m (pc + 1) = holWordExtract 8 15 8 (Encode i) ∧
      m (pc + 2) = holWordExtract 8 23 16 (Encode i) ∧
      m (pc + 3) = holWordExtract 8 31 24 (Encode i) ∧
      dom pc ∧ dom (pc + 1) ∧ dom (pc + 2) ∧ dom (pc + 3) := by
  obtain ⟨a, k, hk, hb⟩ := h
  simp only [riscvConfig, riscvEnc] at hk hb
  rw [show k * 2 ^ 2 = 4 * k by omega] at hk hb
  rw [length_flatMap_riscvEncode] at hk
  rw [drop_flatMap_riscvEncode] at hb
  have hk' : k < (riscvAst a).length := by omega
  rw [List.drop_eq_getElem_cons hk', List.flatMap_cons] at hb
  refine ⟨(riscvAst a)[k], riscvAst_supported a _ (List.getElem_mem hk'), ?_⟩
  simp only [riscvEncode, List.cons_append, bytesInMemoryHOL] at hb
  obtain ⟨h0, d0, h1, d1, h2, d2, h3, d3, -⟩ := hb
  have e1 : pc + 1 + 1 = pc + 2 := by rw [BitVec.add_assoc]; rfl
  have e2 : pc + 2 + 1 = pc + 3 := by rw [BitVec.add_assoc]; rfl
  rw [e1] at h2 d2; rw [e1, e2] at h3 d3
  refine ⟨?_, h0, h1, h2, h3, d0, d1, d2, d3⟩
  simp only [l3Word, h0, h1, h2, h3]
  exact l3Word_bytes _

end RiscvImCompare
