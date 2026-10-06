import RiscvImCompare.SimStep

/-!
# Formalised differences

The simulation needs `SafeL3`. These lemmas show that the memory-access part of
that side condition cannot be dropped: L3 executes every load and store, at
any address and any alignment, while riscv-zkvm traps on misaligned accesses
and on accesses outside its fixed memory map.
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

/-- L3 executes an `LD` at **any** address (no alignment or range check). -/
theorem l3_ld_total {ms : riscv_state} (rd rs1 : BitVec 5) (off : BitVec 12)
    {w : BitVec 32} (h : AtPcW ms w (.Load (.LD (rd, rs1, off)))) :
    ∃ ms', Step.NextRISCV ms = some ms' := by
  have f := (riscvOk_iff ms).mp h.ok
  refine ⟨_, l3_next_normal h («write'GPR» (rawReadData (GPR rs1 ms + BitVec.signExtend 64 off) ms,
    rd) (fetched ms)) ?_ ?_ ?_⟩
  · simp only [Run, «dfn'LD», in32_fetched h.ok, translateAddr, GPR_fetched, Bool.false_eq_true,
      if_false]; rfl
  · simp only [«write'GPR», «write'gpr», fetched]; split <;> simp [f.2.2.2.1]
  · simp only [«write'GPR», «write'gpr», fetched]; split <;> simp [f.2.2.1]

/-- L3 executes an `SD` at **any** address. -/
theorem l3_sd_total {ms : riscv_state} (rs1 rs2 : BitVec 5) (off : BitVec 12)
    {w : BitVec 32} (h : AtPcW ms w (.Store (.SD (rs1, rs2, off)))) :
    ∃ ms', Step.NextRISCV ms = some ms' := by
  have f := (riscvOk_iff ms).mp h.ok
  have hw := rawWriteData_eq (ms := fetched ms) (GPR rs1 ms + BitVec.signExtend 64 off) (GPR rs2 ms) 8
  refine ⟨_, l3_next_normal h (rawWriteData (GPR rs1 ms + BitVec.signExtend 64 off, GPR rs2 ms, 8)
    (fetched ms)) ?_ ?_ ?_⟩
  · simp only [Run, «dfn'SD», in32_fetched h.ok, translateAddr, GPR_fetched, Bool.false_eq_true,
      if_false]
  · rw [hw]; exact f.2.2.2.1
  · rw [hw]; exact f.2.2.1

/-- riscv-zkvm traps on an `LD` whose address is misaligned or outside its memory map. -/
theorem zkvm_ld_traps {s : MachineState} {rd rs1 : RiscvZkvm.Rv64.Reg} {off : BitVec 12}
    (hc : s.code s.pc = some (.LD rd rs1 off))
    (h : RiscvZkvm.Rv64.isValidDwordAccess (s.getReg rs1 + RiscvZkvm.Rv64.signExtend12 off) = false) :
    RiscvZkvm.Rv64.step s = none :=
  RiscvZkvm.Rv64.step_ld_trap hc h

/-- riscv-zkvm traps on an `SD` whose address is misaligned or outside its memory map. -/
theorem zkvm_sd_traps {s : MachineState} {rs1 rs2 : RiscvZkvm.Rv64.Reg} {off : BitVec 12}
    (hc : s.code s.pc = some (.SD rs1 rs2 off))
    (h : RiscvZkvm.Rv64.isValidDwordAccess (s.getReg rs1 + RiscvZkvm.Rv64.signExtend12 off) = false) :
    RiscvZkvm.Rv64.step s = none :=
  RiscvZkvm.Rv64.step_sd_trap hc h

/-- The concrete address `0` (and every address below `0x20`, between
`0x78000000` and `0xa0000000`, or above `0xc0000000`, apart from the input
window) is outside riscv-zkvm's memory map, while it is ordinary memory for L3. -/
theorem zkvm_address_zero_invalid : RiscvZkvm.Rv64.isValidMemAddr 0 = false := by decide

end RiscvImCompare
