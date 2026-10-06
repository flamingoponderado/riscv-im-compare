import RiscvImCompare.Relation
import Flapjack.RiscV.CorrectnessEncoding.DecodeAddi
import Flapjack.RiscV.CorrectnessEncoding.DecodeBinop
import Flapjack.RiscV.CorrectnessEncoding.DecodeBranches
import Flapjack.RiscV.CorrectnessEncoding.DecodeConst
import Flapjack.RiscV.CorrectnessEncoding.DecodeControl
import Flapjack.RiscV.CorrectnessEncoding.DecodeDiv
import Flapjack.RiscV.CorrectnessEncoding.DecodeLongMul
import Flapjack.RiscV.CorrectnessEncoding.DecodeMemory
import Flapjack.RiscV.CorrectnessEncoding.DecodeShift
import Flapjack.RiscV.CorrectnessEncoding.DecodeSltu
import Flapjack.RiscV.CorrectnessEncoding.DecodeUpperImmediates

/-!
# Generic L3 step equations for supported instructions
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target

/-- L3 decodes the encoding of every supported instruction back to itself
(flapjack's per-instruction `decode_encode_*` lemmas). -/
theorem l3_decode_encode (i : instruction) (h : toZ i ≠ none) :
    Step.DecodeAny (.Word (Encode i)) = i := by
  cases i with
  | ArithI j | ArithR j | Branch j | Load j | MulDiv j | Shift j | Store j =>
    cases j <;> rename_i p <;>
      (first
        | obtain ⟨_, _, _⟩ := (p : BitVec 5 × BitVec 5 × _)
        | obtain ⟨_, _⟩ := (p : BitVec 5 × BitVec 20)) <;>
      first
        | exact absurd rfl h
        | simp only [decode_encode_addi, decode_encode_andi, decode_encode_ori, decode_encode_xori, decode_encode_lui, decode_encode_auipc, decode_encode_add, decode_encode_sub, decode_encode_and, decode_encode_or, decode_encode_xor, decode_encode_sltu, decode_encode_sll, decode_encode_srl, decode_encode_sra, decode_encode_slli, decode_encode_srli, decode_encode_srai, decode_encode_mul, decode_encode_mulhu, decode_encode_div, decode_encode_ld, decode_encode_lwu, decode_encode_lhu, decode_encode_lbu, decode_encode_sd, decode_encode_sw, decode_encode_sh, decode_encode_sb, decode_encode_beq, decode_encode_bne, decode_encode_blt, decode_encode_bge, decode_encode_bltu, decode_encode_bgeu, decode_encode_jal, decode_encode_jalr]
  | _ => exact absurd rfl h

/-- Fetching a 32-bit instruction word. -/
theorem l3_fetch (ms : riscv_state) (w : BitVec 32)
    (vm : (ms.c_MCSR ms.procID).mstatus.VM = 0)
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = holWordExtract 8 31 24 w) :
    Step.Fetch ms = (.Word w, fetched ms) := by
  change ms.MEM8 (ms.c_PC ms.procID + 1#64) = _ at b1
  change ms.MEM8 (ms.c_PC ms.procID + 2#64) = _ at b2
  change ms.MEM8 (ms.c_PC ms.procID + 3#64) = _ at b3
  rw [Step.fetch_bare ms vm]
  have lo0 : (holWordExtract 8 7 0 w).getLsbD 0 = true := by
    rw [holWordExtract_eq_extractLsb' w 8 7 0 (by omega) (by omega)]; simpa using low0
  have lo1 : (holWordExtract 8 7 0 w).getLsbD 1 = true := by
    rw [holWordExtract_eq_extractLsb' w 8 7 0 (by omega) (by omega)]; simpa using low1
  simp only [rawReadInst, boolify8, b0, lo0, lo1, Bool.and_self, ite_true, «write'Skip»]
  simp only [b1, b2, b3, fetched]
  simp only [BitVec.setWidth_eq]
  rw [l3Word_bytes' w]
  rfl

/-- Hypotheses for executing the supported instruction `i` at the PC. -/
structure AtPc (ms : riscv_state) (i : instruction) : Prop where
  ok : riscvOk ms = true
  supp : toZ i ≠ none
  b0 : ms.MEM8 (ms.c_PC ms.procID) = holWordExtract 8 7 0 (Encode i)
  b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = holWordExtract 8 15 8 (Encode i)
  b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = holWordExtract 8 23 16 (Encode i)
  b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = holWordExtract 8 31 24 (Encode i)

theorem AtPc.fetch {ms : riscv_state} {i : instruction} (h : AtPc ms i) :
    Step.Fetch ms = (.Word (Encode i), fetched ms) :=
  l3_fetch ms _ ((riscvOk_iff ms).mp h.ok).1 (encode_low_bits i h.supp).1
    (encode_low_bits i h.supp).2 h.b0 h.b1 h.b2 h.b3

/-- Normal (fall-through) control flow. -/
theorem l3_next_normal {ms : riscv_state} {i : instruction} (h : AtPc ms i) (nxt : riscv_state)
    (hrun : Run i (fetched ms) = nxt) (hexc : nxt.exception = .NoException)
    (hnf : nxt.c_NextFetch nxt.procID = none) :
    Step.NextRISCV ms = some («write'PC» (nxt.c_PC nxt.procID + Skip nxt) nxt) :=
  Step.nextRISCV ms _ (fetched ms) i nxt ⟨h.fetch, l3_decode_encode i h.supp, hrun, hexc, hnf⟩

/-- Taken branch / jump. -/
theorem l3_next_branch {ms : riscv_state} {i : instruction} (h : AtPc ms i) (nxt : riscv_state)
    (a : BitVec 64)
    (hrun : Run i (fetched ms) = nxt) (hexc : nxt.exception = .NoException)
    (hnf : nxt.c_NextFetch nxt.procID = some (.BranchTo a)) :
    Step.NextRISCV ms = some («write'PC» a
      { nxt with c_NextFetch := holUpdate nxt.procID none nxt.c_NextFetch }) := by
  rw [Step.nextRISCV_branch ms _ (fetched ms) i nxt a
    ⟨h.fetch, l3_decode_encode i h.supp, hrun, hexc, hnf⟩]
  rfl

end RiscvImCompare
