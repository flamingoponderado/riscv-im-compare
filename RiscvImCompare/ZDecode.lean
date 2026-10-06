import Mathlib.Tactic.IntervalCases
import Flapjack.Misc.Alignment
import RiscvImCompare.Defs

namespace RiscvImCompare

open Flapjack.RiscV.L3
open RiscvZkvm.Rv64 (Instr)
open RiscvZkvm.Interpreter

theorem holWordExtract_eq {a : Nat} (b h l : Nat) (w : BitVec a) :
    holWordExtract b h l w = BitVec.setWidth b (w.extractLsb' l (min h (a - 1) + 1 - l)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [holWordExtract, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_extractLsb', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    BitVec.testBit_toNat]
  by_cases h1 : j < min h (a - 1) + 1 - l
  · by_cases h2 : l + j < a
    · have : j < a := by omega
      simp [h1, this]
    · simp [BitVec.getLsbD_of_ge w (l + j) (by omega)]
  · simp [h1]

theorem holV2w_one (x : Bool) : holV2w 1 [x] = BitVec.ofBool x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [holV2w, Flapjack.getLsbD_holFcpWord]
  interval_cases j; simp

/-- Bit-by-bit proof of a field-extraction identity on an encoding format. -/
macro "bits_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Rtype, Itype, Stype, SBtype, UJtype, Utype, immI, immS, immB, immU, immJ,
    holWordExtract_eq, holV2w_one, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool]
  interval_cases j <;> simp))

section Fields
variable (o : BitVec 7) (f3 : BitVec 3) (rd rs1 rs2 : BitVec 5) (f7 : BitVec 7)
  (imm : BitVec 12) (c sh : BitVec 6) (imm20 : BitVec 20)

theorem rtype_opc : (Rtype (o, f3, rd, rs1, rs2, f7)).extractLsb' 0 7 = o := by bits_tac
theorem rtype_rd : (Rtype (o, f3, rd, rs1, rs2, f7)).extractLsb' 7 5 = rd := by bits_tac
theorem rtype_f3 : (Rtype (o, f3, rd, rs1, rs2, f7)).extractLsb' 12 3 = f3 := by bits_tac
theorem rtype_rs1 : (Rtype (o, f3, rd, rs1, rs2, f7)).extractLsb' 15 5 = rs1 := by bits_tac
theorem rtype_rs2 : (Rtype (o, f3, rd, rs1, rs2, f7)).extractLsb' 20 5 = rs2 := by bits_tac
theorem rtype_f7 : (Rtype (o, f3, rd, rs1, rs2, f7)).extractLsb' 25 7 = f7 := by bits_tac

theorem itype_opc : (Itype (o, f3, rd, rs1, imm)).extractLsb' 0 7 = o := by bits_tac
theorem itype_rd : (Itype (o, f3, rd, rs1, imm)).extractLsb' 7 5 = rd := by bits_tac
theorem itype_f3 : (Itype (o, f3, rd, rs1, imm)).extractLsb' 12 3 = f3 := by bits_tac
theorem itype_rs1 : (Itype (o, f3, rd, rs1, imm)).extractLsb' 15 5 = rs1 := by bits_tac
theorem itype_imm : immI (Itype (o, f3, rd, rs1, imm)) = imm := by bits_tac
theorem itype_f6 :
    (Itype (o, f3, rd, rs1, BitVec.setWidth 12 (c ++ sh))).extractLsb' 26 6 = c := by bits_tac
theorem itype_shamt :
    (Itype (o, f3, rd, rs1, BitVec.setWidth 12 (c ++ sh))).extractLsb' 20 6 = sh := by bits_tac

theorem stype_opc : (Stype (o, f3, rs1, rs2, imm)).extractLsb' 0 7 = o := by bits_tac
theorem stype_f3 : (Stype (o, f3, rs1, rs2, imm)).extractLsb' 12 3 = f3 := by bits_tac
theorem stype_rs1 : (Stype (o, f3, rs1, rs2, imm)).extractLsb' 15 5 = rs1 := by bits_tac
theorem stype_rs2 : (Stype (o, f3, rs1, rs2, imm)).extractLsb' 20 5 = rs2 := by bits_tac
theorem stype_imm : immS (Stype (o, f3, rs1, rs2, imm)) = imm := by bits_tac

theorem sbtype_opc : (SBtype (o, f3, rs1, rs2, imm)).extractLsb' 0 7 = o := by bits_tac
theorem sbtype_f3 : (SBtype (o, f3, rs1, rs2, imm)).extractLsb' 12 3 = f3 := by bits_tac
theorem sbtype_rs1 : (SBtype (o, f3, rs1, rs2, imm)).extractLsb' 15 5 = rs1 := by bits_tac
theorem sbtype_rs2 : (SBtype (o, f3, rs1, rs2, imm)).extractLsb' 20 5 = rs2 := by bits_tac
theorem sbtype_imm : immB (SBtype (o, f3, rs1, rs2, imm)) = imm ++ 0#1 := by bits_tac

theorem utype_opc : (Utype (o, rd, imm20)).extractLsb' 0 7 = o := by bits_tac
theorem utype_rd : (Utype (o, rd, imm20)).extractLsb' 7 5 = rd := by bits_tac
theorem utype_imm : immU (Utype (o, rd, imm20)) = imm20 := by bits_tac

theorem ujtype_opc : (UJtype (o, rd, imm20)).extractLsb' 0 7 = o := by bits_tac
theorem ujtype_rd : (UJtype (o, rd, imm20)).extractLsb' 7 5 = rd := by bits_tac
theorem ujtype_imm : immJ (UJtype (o, rd, imm20)) = imm20 ++ 0#1 := by bits_tac

end Fields

theorem opc_4 : opc (BitVec.ofNat 8 4) = 0x13#7 := by decide
theorem opc_12 : opc (BitVec.ofNat 8 12) = 0x33#7 := by decide
theorem opc_13 : opc (BitVec.ofNat 8 13) = 0x37#7 := by decide
theorem opc_5 : opc (BitVec.ofNat 8 5) = 0x17#7 := by decide
theorem opc_0 : opc (BitVec.ofNat 8 0) = 0x3#7 := by decide
theorem opc_8 : opc (BitVec.ofNat 8 8) = 0x23#7 := by decide
theorem opc_24 : opc (BitVec.ofNat 8 24) = 0x63#7 := by decide
theorem opc_27 : opc (BitVec.ofNat 8 27) = 0x6f#7 := by decide
theorem opc_25 : opc (BitVec.ofNat 8 25) = 0x67#7 := by decide

/-- Rewrites every decoded field of an encoded instruction to its source. -/
macro "decode_tac" : tactic => `(tactic| (
  simp only [Encode, toZ, decode, rtype_opc, rtype_rd, rtype_f3, rtype_rs1, rtype_rs2, rtype_f7,
    itype_opc, itype_rd, itype_f3, itype_rs1, itype_imm, itype_f6, itype_shamt,
    stype_opc, stype_f3, stype_rs1, stype_rs2, stype_imm,
    sbtype_opc, sbtype_f3, sbtype_rs1, sbtype_rs2, sbtype_imm,
    utype_opc, utype_rd, utype_imm, ujtype_opc, ujtype_rd, ujtype_imm,
    opc_4, opc_12, opc_13, opc_5, opc_0, opc_8, opc_24, opc_27, opc_25]
  rfl))

theorem decode_encode_toZ_addi (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.ArithI (.ADDI p))) = toZ (.ArithI (.ADDI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_andi (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.ArithI (.ANDI p))) = toZ (.ArithI (.ANDI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_ori (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.ArithI (.ORI p))) = toZ (.ArithI (.ORI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_xori (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.ArithI (.XORI p))) = toZ (.ArithI (.XORI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_lui (p : BitVec 5 × BitVec 20) :
    decode (Encode (.ArithI (.LUI p))) = toZ (.ArithI (.LUI p)) := by
  rcases p with ⟨_, _⟩
  decode_tac

theorem decode_encode_toZ_auipc (p : BitVec 5 × BitVec 20) :
    decode (Encode (.ArithI (.AUIPC p))) = toZ (.ArithI (.AUIPC p)) := by
  rcases p with ⟨_, _⟩
  decode_tac

theorem decode_encode_toZ_add (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.ArithR (.ADD p))) = toZ (.ArithR (.ADD p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sub (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.ArithR (.SUB p))) = toZ (.ArithR (.SUB p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_and (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.ArithR (.AND p))) = toZ (.ArithR (.AND p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_or (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.ArithR (.OR p))) = toZ (.ArithR (.OR p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_xor (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.ArithR (.XOR p))) = toZ (.ArithR (.XOR p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sltu (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.ArithR (.SLTU p))) = toZ (.ArithR (.SLTU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sll (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.Shift (.SLL p))) = toZ (.Shift (.SLL p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_srl (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.Shift (.SRL p))) = toZ (.Shift (.SRL p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sra (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.Shift (.SRA p))) = toZ (.Shift (.SRA p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_slli (p : BitVec 5 × BitVec 5 × BitVec 6) :
    decode (Encode (.Shift (.SLLI p))) = toZ (.Shift (.SLLI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_srli (p : BitVec 5 × BitVec 5 × BitVec 6) :
    decode (Encode (.Shift (.SRLI p))) = toZ (.Shift (.SRLI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_srai (p : BitVec 5 × BitVec 5 × BitVec 6) :
    decode (Encode (.Shift (.SRAI p))) = toZ (.Shift (.SRAI p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_mul (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.MulDiv (.MUL p))) = toZ (.MulDiv (.MUL p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_mulhu (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.MulDiv (.MULHU p))) = toZ (.MulDiv (.MULHU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_div (p : BitVec 5 × BitVec 5 × BitVec 5) :
    decode (Encode (.MulDiv (.DIV p))) = toZ (.MulDiv (.DIV p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_ld (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Load (.LD p))) = toZ (.Load (.LD p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_lwu (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Load (.LWU p))) = toZ (.Load (.LWU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_lhu (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Load (.LHU p))) = toZ (.Load (.LHU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_lbu (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Load (.LBU p))) = toZ (.Load (.LBU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sd (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Store (.SD p))) = toZ (.Store (.SD p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sw (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Store (.SW p))) = toZ (.Store (.SW p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sh (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Store (.SH p))) = toZ (.Store (.SH p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_sb (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Store (.SB p))) = toZ (.Store (.SB p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_beq (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.BEQ p))) = toZ (.Branch (.BEQ p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_bne (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.BNE p))) = toZ (.Branch (.BNE p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_blt (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.BLT p))) = toZ (.Branch (.BLT p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_bge (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.BGE p))) = toZ (.Branch (.BGE p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_bltu (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.BLTU p))) = toZ (.Branch (.BLTU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_bgeu (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.BGEU p))) = toZ (.Branch (.BGEU p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

theorem decode_encode_toZ_jal (p : BitVec 5 × BitVec 20) :
    decode (Encode (.Branch (.JAL p))) = toZ (.Branch (.JAL p)) := by
  rcases p with ⟨_, _⟩
  decode_tac

theorem decode_encode_toZ_jalr (p : BitVec 5 × BitVec 5 × BitVec 12) :
    decode (Encode (.Branch (.JALR p))) = toZ (.Branch (.JALR p)) := by
  rcases p with ⟨_, _, _⟩
  decode_tac

/-- riscv-zkvm's decoder inverts L3's encoder on every supported instruction, producing
the riscv-zkvm instruction `toZ` assigns to it. -/
theorem decode_encode_toZ (i : Flapjack.RiscV.L3.instruction) (h : RiscvImCompare.toZ i ≠ none) :
    RiscvZkvm.Interpreter.decode (Flapjack.RiscV.L3.Encode i) = RiscvImCompare.toZ i := by
  cases i with
  | ArithI a =>
    cases a with
    | ADDI p => exact decode_encode_toZ_addi p
    | ANDI p => exact decode_encode_toZ_andi p
    | ORI p => exact decode_encode_toZ_ori p
    | XORI p => exact decode_encode_toZ_xori p
    | LUI p => exact decode_encode_toZ_lui p
    | AUIPC p => exact decode_encode_toZ_auipc p
    | _ => exact absurd rfl h
  | ArithR a =>
    cases a with
    | ADD p => exact decode_encode_toZ_add p
    | SUB p => exact decode_encode_toZ_sub p
    | AND p => exact decode_encode_toZ_and p
    | OR p => exact decode_encode_toZ_or p
    | XOR p => exact decode_encode_toZ_xor p
    | SLTU p => exact decode_encode_toZ_sltu p
    | _ => exact absurd rfl h
  | Shift a =>
    cases a with
    | SLL p => exact decode_encode_toZ_sll p
    | SRL p => exact decode_encode_toZ_srl p
    | SRA p => exact decode_encode_toZ_sra p
    | SLLI p => exact decode_encode_toZ_slli p
    | SRLI p => exact decode_encode_toZ_srli p
    | SRAI p => exact decode_encode_toZ_srai p
  | MulDiv a =>
    cases a with
    | MUL p => exact decode_encode_toZ_mul p
    | MULHU p => exact decode_encode_toZ_mulhu p
    | DIV p => exact decode_encode_toZ_div p
    | _ => exact absurd rfl h
  | Load a =>
    cases a with
    | LD p => exact decode_encode_toZ_ld p
    | LWU p => exact decode_encode_toZ_lwu p
    | LHU p => exact decode_encode_toZ_lhu p
    | LBU p => exact decode_encode_toZ_lbu p
    | _ => exact absurd rfl h
  | Store a =>
    cases a with
    | SD p => exact decode_encode_toZ_sd p
    | SW p => exact decode_encode_toZ_sw p
    | SH p => exact decode_encode_toZ_sh p
    | SB p => exact decode_encode_toZ_sb p
  | Branch a =>
    cases a with
    | BEQ p => exact decode_encode_toZ_beq p
    | BNE p => exact decode_encode_toZ_bne p
    | BLT p => exact decode_encode_toZ_blt p
    | BGE p => exact decode_encode_toZ_bge p
    | BLTU p => exact decode_encode_toZ_bltu p
    | BGEU p => exact decode_encode_toZ_bgeu p
    | JAL p => exact decode_encode_toZ_jal p
    | JALR p => exact decode_encode_toZ_jalr p
  | _ => exact absurd rfl h

end RiscvImCompare
