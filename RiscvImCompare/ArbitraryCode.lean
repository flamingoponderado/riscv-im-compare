import RiscvImCompare.ArbitraryStep
import RiscvImCompare.DecodeAgree

/-!
# Arbitrary code: decoder agreement plugged into the step comparison

Outside the SYSTEM opcode `0x73` the two decoders agree on every 32-bit word
(`decode_eq_toZx`), so the decoder hypothesis of `step_sim_word` / `run_sim`
reduces to "the opcode is not `0x73`".
-/

namespace RiscvImCompare

open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target
open RiscvZkvm.Interpreter (regOfBits decode)

/-- **Single step of arbitrary non-SYSTEM code.** If the word at the PC is not
a SYSTEM instruction, L3 decodes it to a shared instruction, and its memory
access is safe, then both models step to related states. -/
theorem step_sim_nonsystem (C : BitVec 64 → Prop) (ms : riscv_state) (z : ZState)
    (hR : Rel C ms z) (hok : riscvOk ms = true) (hpc : C (ms.c_PC ms.procID))
    (hop : (l3Word ms.MEM8 (ms.c_PC ms.procID)).extractLsb' 0 7 ≠ 0x73#7)
    (hsup : toZx (Decode (l3Word ms.MEM8 (ms.c_PC ms.procID))) ≠ none)
    (hms : MemSafeX C ms (Decode (l3Word ms.MEM8 (ms.c_PC ms.procID)))) :
    StepsAgree C ms z :=
  step_sim_word C ms z hR hok hpc _ rfl hsup (decode_eq_toZx _ hop) hms

/-- Outside SYSTEM, a word that L3 does not decode to a shared instruction is
also rejected by riscv-zkvm's decoder (so riscv-zkvm traps on it). -/
theorem both_reject_nonsystem (w : BitVec 32) (hop : w.extractLsb' 0 7 ≠ 0x73#7)
    (hnone : toZx (Decode w) = none) : decode w = none := by
  rw [decode_eq_toZx w hop, hnone]

/-- `SafeWord` for non-SYSTEM code, without any decoder hypothesis. -/
def SafeWordNS (C : BitVec 64 → Prop) (ms : riscv_state) : Prop :=
  riscvOk ms = true ∧ C (ms.c_PC ms.procID) ∧
    (l3Word ms.MEM8 (ms.c_PC ms.procID)).extractLsb' 0 7 ≠ 0x73#7 ∧
    toZx (Decode (l3Word ms.MEM8 (ms.c_PC ms.procID))) ≠ none ∧
    MemSafeX C ms (Decode (l3Word ms.MEM8 (ms.c_PC ms.procID)))

theorem SafeWordNS.safeWord {C : BitVec 64 → Prop} {ms : riscv_state} (h : SafeWordNS C ms) :
    SafeWord C ms :=
  ⟨h.1, h.2.1, _, rfl, h.2.2.2.1, decode_eq_toZx _ h.2.2.1, h.2.2.2.2⟩

/-- **Lockstep runs of arbitrary non-SYSTEM code.** -/
theorem run_sim_nonsystem (C : BitVec 64 → Prop) (n : Nat) (ms : riscv_state) (z : ZState)
    (hR : Rel C ms z)
    (hs : ∀ k < n, ∀ ms', l3StepN k ms = some ms' → SafeWordNS C ms') :
    ∃ ms' z', l3StepN n ms = some ms' ∧ RiscvZkvm.Rv64.stepN n z.m = some z'.m ∧
      Rel C ms' z' :=
  run_sim C n ms z hR (fun k hk ms' h => (hs k hk ms' h).safeWord)

end RiscvImCompare
