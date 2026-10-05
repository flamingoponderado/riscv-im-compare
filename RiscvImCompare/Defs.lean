import Flapjack.Compiler.Encoders.RiscV.Target.State
import RiscvZkvm.Rv64
import RiscvZkvm.Interpreter.Decode

/-!
# Shared definitions for comparing flapjack's L3 RISC-V model with riscv-zkvm

* `toZ` maps the 37 kinds of L3 instructions that flapjack's RISC-V encoder can
  emit to the riscv-zkvm `Instr` they denote. It is `none` on every other
  instruction, so `toZ i ≠ none` is the "supported instruction" predicate.
* `l3Dword` reads a little-endian doubleword out of L3's byte memory, and
  `MemRel` says riscv-zkvm's doubleword memory agrees with L3's byte memory at
  every 8-aligned address.
* `l3Word` reads the 32-bit instruction word at an address of L3's byte memory.
-/

namespace RiscvImCompare

open Flapjack.RiscV.L3
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

/-- The riscv-zkvm instruction denoted by an L3 instruction, for the 37 kinds of
instruction that flapjack's RISC-V encoder (`riscvAst`) can produce; `none`
otherwise. Branch and jump offsets are stored in half-words by L3 and in bytes by
riscv-zkvm, hence the appended zero bit. -/
def toZ : instruction → Option Instr
  | .ArithI (.ADDI (rd, rs1, imm)) => some (.ADDI (regOfBits rd) (regOfBits rs1) imm)
  | .ArithI (.ANDI (rd, rs1, imm)) => some (.ANDI (regOfBits rd) (regOfBits rs1) imm)
  | .ArithI (.ORI (rd, rs1, imm)) => some (.ORI (regOfBits rd) (regOfBits rs1) imm)
  | .ArithI (.XORI (rd, rs1, imm)) => some (.XORI (regOfBits rd) (regOfBits rs1) imm)
  | .ArithI (.LUI (rd, imm)) => some (.LUI (regOfBits rd) imm)
  | .ArithI (.AUIPC (rd, imm)) => some (.AUIPC (regOfBits rd) imm)
  | .ArithR (.ADD (rd, rs1, rs2)) => some (.ADD (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .ArithR (.SUB (rd, rs1, rs2)) => some (.SUB (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .ArithR (.AND (rd, rs1, rs2)) => some (.AND (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .ArithR (.OR (rd, rs1, rs2)) => some (.OR (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .ArithR (.XOR (rd, rs1, rs2)) => some (.XOR (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .ArithR (.SLTU (rd, rs1, rs2)) =>
    some (.SLTU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .Shift (.SLL (rd, rs1, rs2)) => some (.SLL (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .Shift (.SRL (rd, rs1, rs2)) => some (.SRL (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .Shift (.SRA (rd, rs1, rs2)) => some (.SRA (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .Shift (.SLLI (rd, rs1, sh)) => some (.SLLI (regOfBits rd) (regOfBits rs1) sh)
  | .Shift (.SRLI (rd, rs1, sh)) => some (.SRLI (regOfBits rd) (regOfBits rs1) sh)
  | .Shift (.SRAI (rd, rs1, sh)) => some (.SRAI (regOfBits rd) (regOfBits rs1) sh)
  | .MulDiv (.MUL (rd, rs1, rs2)) => some (.MUL (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .MulDiv (.MULHU (rd, rs1, rs2)) =>
    some (.MULHU (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .MulDiv (.DIV (rd, rs1, rs2)) => some (.DIV (regOfBits rd) (regOfBits rs1) (regOfBits rs2))
  | .Load (.LD (rd, rs1, off)) => some (.LD (regOfBits rd) (regOfBits rs1) off)
  | .Load (.LWU (rd, rs1, off)) => some (.LWU (regOfBits rd) (regOfBits rs1) off)
  | .Load (.LHU (rd, rs1, off)) => some (.LHU (regOfBits rd) (regOfBits rs1) off)
  | .Load (.LBU (rd, rs1, off)) => some (.LBU (regOfBits rd) (regOfBits rs1) off)
  | .Store (.SD (rs1, rs2, off)) => some (.SD (regOfBits rs1) (regOfBits rs2) off)
  | .Store (.SW (rs1, rs2, off)) => some (.SW (regOfBits rs1) (regOfBits rs2) off)
  | .Store (.SH (rs1, rs2, off)) => some (.SH (regOfBits rs1) (regOfBits rs2) off)
  | .Store (.SB (rs1, rs2, off)) => some (.SB (regOfBits rs1) (regOfBits rs2) off)
  | .Branch (.BEQ (rs1, rs2, off)) => some (.BEQ (regOfBits rs1) (regOfBits rs2) (off ++ 0#1))
  | .Branch (.BNE (rs1, rs2, off)) => some (.BNE (regOfBits rs1) (regOfBits rs2) (off ++ 0#1))
  | .Branch (.BLT (rs1, rs2, off)) => some (.BLT (regOfBits rs1) (regOfBits rs2) (off ++ 0#1))
  | .Branch (.BGE (rs1, rs2, off)) => some (.BGE (regOfBits rs1) (regOfBits rs2) (off ++ 0#1))
  | .Branch (.BLTU (rs1, rs2, off)) =>
    some (.BLTU (regOfBits rs1) (regOfBits rs2) (off ++ 0#1))
  | .Branch (.BGEU (rs1, rs2, off)) =>
    some (.BGEU (regOfBits rs1) (regOfBits rs2) (off ++ 0#1))
  | .Branch (.JAL (rd, imm)) => some (.JAL (regOfBits rd) (imm ++ 0#1))
  | .Branch (.JALR (rd, rs1, imm)) => some (.JALR (regOfBits rd) (regOfBits rs1) imm)
  | _ => none

/-- Little-endian doubleword at `a` in L3's byte memory. -/
def l3Dword (m : BitVec 64 → BitVec 8) (a : BitVec 64) : BitVec 64 :=
  m (a + 7) ++ m (a + 6) ++ m (a + 5) ++ m (a + 4) ++ m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a

/-- Little-endian 32-bit word at `a` in L3's byte memory (the fetched instruction). -/
def l3Word (m : BitVec 64 → BitVec 8) (a : BitVec 64) : BitVec 32 :=
  m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a

/-- riscv-zkvm's doubleword memory agrees with L3's byte memory on every
8-aligned doubleword. (riscv-zkvm only ever reads `mem` at 8-aligned addresses:
`getByte`/`getHalfword`/`getWord32` align down, and `LD`/`SD` trap unless
aligned.) -/
def MemRel (m : BitVec 64 → BitVec 8) (zm : BitVec 64 → BitVec 64) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → zm a = l3Dword m a

end RiscvImCompare
