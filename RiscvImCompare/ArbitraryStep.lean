import RiscvImCompare.SimShared

/-!
# Single-step comparison on arbitrary instruction words

For submitted (non-compiler) code the relevant statement is about an
*arbitrary* 32-bit word at the PC. `step_sim_word` covers every instruction both
models implement except `ECALL`/`EBREAK` (the 50 instructions of `toZx`); it
takes the decoder agreement for the word as a hypothesis (`decode w = toZx i`,
discharged separately by the decoder comparison). `ECALL` and `EBREAK` are
characterised separately: L3 never completes such a step.
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target
open RiscvZkvm.Rv64 (Instr MachineState)
open RiscvZkvm.Interpreter (regOfBits decode)

/-- `MemSafe` extended to the signed loads `LW`/`LH`/`LB`. -/
def MemSafeX (C : BitVec 64 → Prop) (ms : riscv_state) : instruction → Prop
  | .Load (.LW (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidMemAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | .Load (.LH (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidHalfwordAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | .Load (.LB (_, rs1, off)) =>
    RiscvZkvm.Rv64.isValidByteAccess (GPR rs1 ms + BitVec.signExtend 64 off) = true
  | i => MemSafe C ms i

theorem l3Word_byte0 (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    m a = holWordExtract 8 7 0 (l3Word m a) := by
  rw [holWordExtract_eq_extractLsb' _ 8 7 0 (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [l3Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases j <;> simp
theorem l3Word_byte1 (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    m (a + 1) = holWordExtract 8 15 8 (l3Word m a) := by
  rw [holWordExtract_eq_extractLsb' _ 8 15 8 (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [l3Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases j <;> simp
theorem l3Word_byte2 (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    m (a + 2) = holWordExtract 8 23 16 (l3Word m a) := by
  rw [holWordExtract_eq_extractLsb' _ 8 23 16 (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [l3Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases j <;> simp
theorem l3Word_byte3 (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    m (a + 3) = holWordExtract 8 31 24 (l3Word m a) := by
  rw [holWordExtract_eq_extractLsb' _ 8 31 24 (by omega) (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [l3Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases j <;> simp

/-- **Single-step agreement on an arbitrary instruction word.** Let `w` be the
word at the PC (which lies in the program `C`), `i` its L3 decoding, and
suppose `i` is one of the 50 shared instructions (`toZx i ≠ none`), riscv-zkvm
decodes `w` to the corresponding instruction, and memory accesses are safe.
Then L3 and riscv-zkvm both step, to related states. -/
theorem step_sim_word (C : BitVec 64 → Prop) (ms : riscv_state) (z : ZState) (hR : Rel C ms z)
    (hok : riscvOk ms = true) (hpc : C (ms.c_PC ms.procID)) (i : instruction)
    (hdecL3 : Decode (l3Word ms.MEM8 (ms.c_PC ms.procID)) = i) (hi : toZx i ≠ none)
    (hdecZ : decode (l3Word ms.MEM8 (ms.c_PC ms.procID)) = toZx i)
    (hms : MemSafeX C ms i) : StepsAgree C ms z := by
  set w := l3Word ms.MEM8 (ms.c_PC ms.procID) with hw
  have hlow := decode_low_bits w (by rw [hdecZ]; exact hi)
  have hat : AtPcW ms w i := ⟨hok, hlow.1, hlow.2, l3Word_byte0 _ _, l3Word_byte1 _ _,
    l3Word_byte2 _ _, l3Word_byte3 _ _, hdecL3⟩
  have hc : z.m.code z.m.pc = toZx i := by rw [← hR.pc, hR.code _ hpc, ← hdecZ]
  clear_value w
  cases i with
  | ArithI j | ArithR j | Branch j | Load j | MulDiv j | Shift j | Store j =>
    cases j <;> rename_i p <;>
      (first
        | obtain ⟨_, _, _⟩ := (p : BitVec 5 × BitVec 5 × _)
        | obtain ⟨_, _⟩ := (p : BitVec 5 × BitVec 20)) <;>
      first
      | exact absurd rfl hi
      | exact sim_ADD hR _ _ _ hat hc | exact sim_SUB hR _ _ _ hat hc
      | exact sim_AND hR _ _ _ hat hc | exact sim_OR hR _ _ _ hat hc
      | exact sim_XOR hR _ _ _ hat hc | exact sim_SLTU hR _ _ _ hat hc
      | exact sim_SLL hR _ _ _ hat hc | exact sim_SRL hR _ _ _ hat hc
      | exact sim_SRA hR _ _ _ hat hc | exact sim_MUL hR _ _ _ hat hc
      | exact sim_MULHU hR _ _ _ hat hc | exact sim_DIV hR _ _ _ hat hc
      | exact sim_SLLI hR _ _ _ hat hc | exact sim_SRLI hR _ _ _ hat hc
      | exact sim_SRAI hR _ _ _ hat hc | exact sim_ADDI hR _ _ _ hat hc
      | exact sim_ANDI hR _ _ _ hat hc | exact sim_ORI hR _ _ _ hat hc
      | exact sim_XORI hR _ _ _ hat hc | exact sim_LUI hR _ _ hat hc
      | exact sim_AUIPC hR _ _ hat hc | exact sim_JAL hR _ _ hat hc
      | exact sim_JALR hR _ _ _ hat hc | exact sim_BEQ hR _ _ _ hat hc
      | exact sim_BNE hR _ _ _ hat hc | exact sim_BLT hR _ _ _ hat hc
      | exact sim_BGE hR _ _ _ hat hc | exact sim_BLTU hR _ _ _ hat hc
      | exact sim_BGEU hR _ _ _ hat hc
      | exact sim_LD hR _ _ _ hat hc hms | exact sim_LWU hR _ _ _ hat hc hms
      | exact sim_LHU hR _ _ _ hat hc hms | exact sim_LBU hR _ _ _ hat hc hms
      | exact sim_SD hR _ _ _ hat hc hms | exact sim_SW hR _ _ _ hat hc hms
      | exact sim_SH hR _ _ _ hat hc hms | exact sim_SB hR _ _ _ hat hc hms
      | exact sim_SLT hR _ _ _ hat hc | exact sim_SLTI hR _ _ _ hat hc
      | exact sim_SLTIU hR _ _ _ hat hc | exact sim_ADDIW hR _ _ _ hat hc
      | exact sim_MULH hR _ _ _ hat hc | exact sim_MULHSU hR _ _ _ hat hc
      | exact sim_DIVU hR _ _ _ hat hc | exact sim_REM hR _ _ _ hat hc
      | exact sim_REMU hR _ _ _ hat hc
      | exact sim_LW hR _ _ _ hat hc hms | exact sim_LH hR _ _ _ hat hc hms
      | exact sim_LB hR _ _ _ hat hc hms
  | FENCE p => exact sim_FENCE hR p hat hc
  | _ => exact absurd rfl hi

/-! ## ECALL and EBREAK -/

/-- L3 never completes an `ECALL` step: it raises an environment-call exception,
so `NextRISCV` is `none` (and flapjack's `riscvNext` is the unspecified
`holThe none`). riscv-zkvm instead runs its syscall ABI (`RiscvZkvm.Rv64.step`). -/
theorem l3_ecall_none {ms : riscv_state} {w : BitVec 32} (h : AtPcW ms w (.System .ECALL)) :
    Step.NextRISCV ms = none := by
  obtain ⟨t, ht⟩ : ∃ t, NextFetch (Run (.System .ECALL) (fetched ms)) = some (.Trap t) := by
    simp only [Run, «dfn'ECALL», signalEnvCall, signalException, setTrap, «write'NextFetch», NextFetch,
      holUpdate, if_true]
    exact ⟨_, rfl⟩
  rw [Step.NextRISCV_equation, h.fetch]
  dsimp only
  rw [h.dec]
  split
  · rfl
  · rw [ht]

/-- L3 never completes an `EBREAK` step (breakpoint exception); riscv-zkvm traps
too (`RiscvZkvm.Rv64.step_ebreak`). -/
theorem l3_ebreak_none {ms : riscv_state} {w : BitVec 32} (h : AtPcW ms w (.System .EBREAK)) :
    Step.NextRISCV ms = none := by
  obtain ⟨t, ht⟩ : ∃ t, NextFetch (Run (.System .EBREAK) (fetched ms)) = some (.Trap t) := by
    simp only [Run, «dfn'EBREAK», signalException, setTrap, «write'NextFetch», NextFetch,
      holUpdate, if_true]
    exact ⟨_, rfl⟩
  rw [Step.NextRISCV_equation, h.fetch]
  dsimp only
  rw [h.dec]
  split
  · rfl
  · rw [ht]

/-! ## Multi-step runs of arbitrary code -/

/-- `n` steps of L3 (`none` as soon as a step does not complete). -/
noncomputable def l3StepN : Nat → riscv_state → Option riscv_state
  | 0, s => some s
  | n + 1, s => (Step.NextRISCV s).bind (l3StepN n)

/-- The per-step side condition for arbitrary code: the state is ok, the PC is
in the program `C`, the word there is one of the 50 shared instructions on
which both decoders agree, and its memory access (if any) is safe. -/
def SafeWord (C : BitVec 64 → Prop) (ms : riscv_state) : Prop :=
  riscvOk ms = true ∧ C (ms.c_PC ms.procID) ∧
    ∃ i, Decode (l3Word ms.MEM8 (ms.c_PC ms.procID)) = i ∧ toZx i ≠ none ∧
      decode (l3Word ms.MEM8 (ms.c_PC ms.procID)) = toZx i ∧ MemSafeX C ms i

/-- **Lockstep runs on arbitrary code.** If every state reached by the first
`n` L3 steps satisfies `SafeWord`, then both models complete `n` steps, to
related states. -/
theorem run_sim (C : BitVec 64 → Prop) :
    ∀ (n : Nat) (ms : riscv_state) (z : ZState), Rel C ms z →
      (∀ k < n, ∀ ms', l3StepN k ms = some ms' → SafeWord C ms') →
      ∃ ms' z', l3StepN n ms = some ms' ∧ RiscvZkvm.Rv64.stepN n z.m = some z'.m ∧
        Rel C ms' z'
  | 0, ms, z, hR, _ => ⟨ms, z, rfl, rfl, hR⟩
  | n + 1, ms, z, hR, hs => by
    obtain ⟨hok, hpc, i, hdL, hi, hdZ, hm⟩ := hs 0 (by omega) ms rfl
    obtain ⟨ms1, m1, h1, h2, hR1⟩ := step_sim_word C ms z hR hok hpc i hdL hi hdZ hm
    obtain ⟨ms', z', h3, h4, hR'⟩ := run_sim C n ms1 ⟨m1, true⟩ hR1 (by
      intro k hk ms' hk'
      exact hs (k + 1) (by omega) ms' (by simp [l3StepN, h1, hk']))
    refine ⟨ms', z', ?_, ?_, hR'⟩
    · simp [l3StepN, h1, h3]
    · simp [RiscvZkvm.Rv64.stepN, h2]; exact h4

end RiscvImCompare
