import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem

/-!
# Generic lockstep simulation for flapjack's target machine semantics

Flapjack's observable machine semantics `machineSemHOL` (a port of CakeML's
`machine_sem`) is generic in the machine-state type: it only looks at a machine
state through the `HolAsmTarget` record (`next`, `getPc`, `getReg`, `getByte`,
`stateOk`, `config`) and through the environment oracles of the
`MachineConfig` (`nextInterfer`, `ffiInterfer`, `ccacheInterfer`).

This file proves, once and for all, that two machine configurations over
*different* state types have the same clocked evaluation (same result, same
FFI state and therefore the same I/O trace) and hence the same set of
behaviours, provided there is a relation `R` between their states which

* makes all the observations agree (`getPc`, `getReg`, `getByte`, `stateOk`),
* is preserved by `next` whenever the evaluator actually calls `next`
  (`StepGuard`) **and** a user-chosen side condition `Safe` holds, and
* is preserved by the environment oracles.

`Safe` is the place where the two step functions are allowed to disagree: the
simulation is only claimed for runs of the first machine that never take a
step outside `Safe` (`RunSafe`).
-/

namespace RiscvImCompare

open Flapjack Flapjack.Compiler.Encoders.Asm

section

variable {w : Nat} [NeZero w] {S S1 S2 P P1 P2 σ : Type}

/-- The situation in which `evaluateTargetHOL` calls `mc.target.next`: the
current state is ok, the PC is a program address that is not an FFI entry
point, and the bytes at the PC are (part of) the encoding of some `asm`
instruction. -/
def StepGuard (mc : MachineConfig w S P) (s : S) : Prop :=
  mc.target.stateOk s = true ∧ mc.progAddresses (mc.target.getPc s) ∧
    mc.target.getPc s ∉ mc.ffiEntryPcs ∧
    encodedBytesInMemHOL mc.target.config (mc.target.getPc s) (mc.target.getByte s)
      mc.progAddresses

/-- Hypotheses of the generic simulation theorem. All non-state fields of the
two machine configurations agree, the observations agree on related states,
and `R` is preserved by the step function (on `Safe` guarded states) and by
every environment oracle. -/
structure SimConfig (mc1 : MachineConfig w S1 P1) (mc2 : MachineConfig w S2 P2)
    (R : S1 → S2 → Prop) (Safe : S1 → Prop) : Prop where
  progAddresses : mc1.progAddresses = mc2.progAddresses
  sharedAddresses : mc1.sharedAddresses = mc2.sharedAddresses
  ffiEntryPcs : mc1.ffiEntryPcs = mc2.ffiEntryPcs
  ffiNames : mc1.ffiNames = mc2.ffiNames
  ptrReg : mc1.ptrReg = mc2.ptrReg
  lenReg : mc1.lenReg = mc2.lenReg
  ptr2Reg : mc1.ptr2Reg = mc2.ptr2Reg
  len2Reg : mc1.len2Reg = mc2.len2Reg
  haltPc : mc1.haltPc = mc2.haltPc
  ccachePc : mc1.ccachePc = mc2.ccachePc
  mmioInfo : mc1.mmioInfo = mc2.mmioInfo
  config : mc1.target.config = mc2.target.config
  getPc : ∀ s1 s2, R s1 s2 → mc1.target.getPc s1 = mc2.target.getPc s2
  getReg : ∀ s1 s2, R s1 s2 → mc1.target.getReg s1 = mc2.target.getReg s2
  getByte : ∀ s1 s2, R s1 s2 → mc1.target.getByte s1 = mc2.target.getByte s2
  stateOk : ∀ s1 s2, R s1 s2 → mc1.target.stateOk s1 = mc2.target.stateOk s2
  next : ∀ s1 s2, R s1 s2 → StepGuard mc1 s1 → Safe s1 →
    R (mc1.target.next s1) (mc2.target.next s2)
  nextInterfer : ∀ n s1 s2, R s1 s2 → R (mc1.nextInterfer n s1) (mc2.nextInterfer n s2)
  ffiInterfer : ∀ n i bs s1 s2, R s1 s2 →
    R (mc1.ffiInterfer n (i, bs, s1)) (mc2.ffiInterfer n (i, bs, s2))
  ccacheInterfer : ∀ n a b s1 s2, R s1 s2 →
    R (mc1.ccacheInterfer n (a, b, s1)) (mc2.ccacheInterfer n (a, b, s2))

/-- Every guarded step taken by the first machine during the first `k` clock
ticks satisfies `Safe`. The `j`-th state of the run is the state returned
with `TimeOut` by the evaluator with clock `j`. -/
def RunSafeUpTo (mc : MachineConfig w S P) (ffi : HolFfiState σ) (Safe : S → Prop)
    (k : Nat) (s : S) : Prop :=
  ∀ j, j < k → ∀ s' f', evaluateTargetHOL mc ffi j s = (.timeOut, s', f') →
    StepGuard mc s' → Safe s'

/-- Every guarded step taken by the first machine satisfies `Safe`. -/
def RunSafe (mc : MachineConfig w S P) (ffi : HolFfiState σ) (Safe : S → Prop)
    (s : S) : Prop :=
  ∀ k, RunSafeUpTo mc ffi Safe k s

/-- Corresponding evaluator results: equal machine result, equal FFI state
(hence equal I/O trace), and related final machine states. -/
def ResultCorr (R : S1 → S2 → Prop)
    (r1 : MachineResult × S1 × HolFfiState σ) (r2 : MachineResult × S2 × HolFfiState σ) :
    Prop :=
  r1.1 = r2.1 ∧ r1.2.2 = r2.2.2 ∧ R r1.2.1 r2.2.1

theorem SimConfig.withNextInterfer {mc1 : MachineConfig w S1 P1} {mc2 : MachineConfig w S2 P2}
    {R : S1 → S2 → Prop} {Safe : S1 → Prop} (h : SimConfig mc1 mc2 R Safe) :
    SimConfig { mc1 with nextInterfer := holShiftSeq 1 mc1.nextInterfer }
      { mc2 with nextInterfer := holShiftSeq 1 mc2.nextInterfer } R Safe :=
  { h with
    next := fun s1 s2 hr hg hs => h.next s1 s2 hr hg hs
    nextInterfer := fun n s1 s2 hr => h.nextInterfer (n + 1) s1 s2 hr }

theorem SimConfig.withFfiInterfer {mc1 : MachineConfig w S1 P1} {mc2 : MachineConfig w S2 P2}
    {R : S1 → S2 → Prop} {Safe : S1 → Prop} (h : SimConfig mc1 mc2 R Safe) :
    SimConfig { mc1 with ffiInterfer := holShiftSeq 1 mc1.ffiInterfer }
      { mc2 with ffiInterfer := holShiftSeq 1 mc2.ffiInterfer } R Safe :=
  { h with
    next := fun s1 s2 hr hg hs => h.next s1 s2 hr hg hs
    ffiInterfer := fun n i bs s1 s2 hr => h.ffiInterfer (n + 1) i bs s1 s2 hr }

theorem SimConfig.withCcacheInterfer {mc1 : MachineConfig w S1 P1}
    {mc2 : MachineConfig w S2 P2}
    {R : S1 → S2 → Prop} {Safe : S1 → Prop} (h : SimConfig mc1 mc2 R Safe) :
    SimConfig { mc1 with ccacheInterfer := holShiftSeq 1 mc1.ccacheInterfer }
      { mc2 with ccacheInterfer := holShiftSeq 1 mc2.ccacheInterfer } R Safe :=
  { h with
    next := fun s1 s2 hr hg hs => h.next s1 s2 hr hg hs
    ccacheInterfer := fun n a b s1 s2 hr => h.ccacheInterfer (n + 1) a b s1 s2 hr }

/-- Shifting the run-safety window by one evaluator step. -/
theorem RunSafeUpTo.tail {mc mc' : MachineConfig w S P} {ffi ffi' : HolFfiState σ}
    {Safe : S → Prop} {k : Nat} {s s' : S}
    (hguard : ∀ t, StepGuard mc' t → StepGuard mc t)
    (heval : ∀ j, evaluateTargetHOL mc ffi (j + 1) s = evaluateTargetHOL mc' ffi' j s')
    (h : RunSafeUpTo mc ffi Safe (k + 1) s) : RunSafeUpTo mc' ffi' Safe k s' := by
  intro j hj t f ht hg
  exact h (j + 1) (by omega) t f (by rw [heval]; exact ht) (hguard t hg)

theorem isValidMappedRead_congr {S1 S2 P1 P2 rp : Type} (t1 : HolAsmTarget w S1 P1)
    (t2 : HolAsmTarget w S2 P2) (s1 : S1) (s2 : S2) (pc : BitVec w) (nb : BitVec 8)
    (a : HolAddr w) (r : Nat) (ret : rp) (d : BitVec w → Prop)
    (hc : t1.config = t2.config) (hb : t1.getByte s1 = t2.getByte s2) :
    isValidMappedRead pc nb a r ret t1 s1 d ↔ isValidMappedRead pc nb a r ret t2 s2 d := by
  simp only [isValidMappedRead, hc, hb]

theorem isValidMappedWrite_congr {S1 S2 P1 P2 rp : Type} (t1 : HolAsmTarget w S1 P1)
    (t2 : HolAsmTarget w S2 P2) (s1 : S1) (s2 : S2) (pc : BitVec w) (nb : BitVec 8)
    (a : HolAddr w) (r : Nat) (ret : rp) (d : BitVec w → Prop)
    (hc : t1.config = t2.config) (hb : t1.getByte s1 = t2.getByte s2) :
    isValidMappedWrite pc nb a r ret t1 s1 d ↔ isValidMappedWrite pc nb a r ret t2 s2 d := by
  simp only [isValidMappedWrite, hc, hb]

theorem readFfiBytearrays_congr {mc1 : MachineConfig w S1 P1} {mc2 : MachineConfig w S2 P2}
    {R : S1 → S2 → Prop} {Safe : S1 → Prop} (h : SimConfig mc1 mc2 R Safe)
    {s1 : S1} {s2 : S2} (hr : R s1 s2) :
    readFfiBytearraysHOL mc1 s1 = readFfiBytearraysHOL mc2 s2 := by
  simp only [readFfiBytearraysHOL, readFfiBytearrayHOL, h.getReg s1 s2 hr,
    h.getByte s1 s2 hr, h.ptrReg, h.lenReg, h.ptr2Reg, h.len2Reg]
  rw [h.progAddresses]

/-! ## One-step unfolding equations of the evaluator -/

section Unfold
variable {S P : Type}

theorem eval_next_eq (mc : MachineConfig w S P) (ffi : HolFfiState σ) (j : Nat) (s : S)
    (hA : mc.progAddresses (mc.target.getPc s) ∧ mc.target.getPc s ∉ mc.ffiEntryPcs)
    (hB : encodedBytesInMemHOL mc.target.config (mc.target.getPc s) (mc.target.getByte s) mc.progAddresses)
    (hC : mc.target.stateOk s = true ∧
              mc.target.stateOk (mc.target.next s) = true ∧
                mc.target.stateOk (mc.nextInterfer 0 (mc.target.next s)) = true ∧
                  ∀ (x : BitVec w),
                    ¬mc.progAddresses x →
                      mc.target.getByte (mc.target.next s) x = mc.target.getByte s x) :
    evaluateTargetHOL mc ffi (j + 1) s =
      evaluateTargetHOL { mc with nextInterfer := holShiftSeq 1 mc.nextInterfer } ffi j
        (mc.nextInterfer 0 (mc.target.next s)) := by
  rw [evaluateTargetHOL]
  simp only [applyOracleHOL]
  rw [if_pos hA, if_pos hB]
  exact if_pos hC

theorem eval_ccache_eq (mc : MachineConfig w S P) (ffi : HolFfiState σ) (j : Nat) (s : S)
    (hA : ¬ (mc.progAddresses (mc.target.getPc s) ∧ mc.target.getPc s ∉ mc.ffiEntryPcs))
    (hH : mc.target.getPc s ≠ mc.haltPc) (hC : mc.target.getPc s = mc.ccachePc) :
    evaluateTargetHOL mc ffi (j + 1) s =
      evaluateTargetHOL { mc with ccacheInterfer := holShiftSeq 1 mc.ccacheInterfer } ffi j
        (mc.ccacheInterfer 0 (mc.target.getReg s mc.ptrReg, mc.target.getReg s mc.lenReg, s)) := by
  rw [evaluateTargetHOL]
  simp only [applyOracleHOL]
  rw [if_neg hA, if_neg hH, if_pos hC]

theorem eval_ffi_ext_eq (mc : MachineConfig w S P) (ffi : HolFfiState σ) (j : Nat) (s : S)
    (hA : ¬ (mc.progAddresses (mc.target.getPc s) ∧ mc.target.getPc s ∉ mc.ffiEntryPcs))
    (hH : mc.target.getPc s ≠ mc.haltPc) (hC : mc.target.getPc s ≠ mc.ccachePc)
    (index : Nat) (hfi : Misc.findIndex (mc.target.getPc s) mc.ffiEntryPcs 0 = some index)
    (name : _) (hname : holEl index mc.ffiNames = .extCall name)
    (hlookup : sptAListLookup index mc.mmioInfo = none)
    (b1 b2 : List (BitVec 8)) (hread : readFfiBytearraysHOL mc s = (some b1, some b2))
    (newFfi : HolFfiState σ) (newBytes : List (BitVec 8))
    (hcall : callFFIHOL ffi (holEl index mc.ffiNames) b1 b2 = .ret newFfi newBytes) :
    evaluateTargetHOL mc ffi (j + 1) s =
      evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } newFfi j
        (mc.ffiInterfer 0 (index, newBytes, s)) := by
  rw [evaluateTargetHOL]
  simp only [applyOracleHOL]
  rw [if_neg hA, if_neg hH, if_neg hC]
  simp only [hfi, hname, hlookup, hread]
  rw [← hname, hcall]

theorem eval_ffi_read_eq (mc : MachineConfig w S P) (ffi : HolFfiState σ) (j : Nat) (s : S)
    (hA : ¬ (mc.progAddresses (mc.target.getPc s) ∧ mc.target.getPc s ∉ mc.ffiEntryPcs))
    (hH : mc.target.getPc s ≠ mc.haltPc) (hC : mc.target.getPc s ≠ mc.ccachePc)
    (index : Nat) (hfi : Misc.findIndex (mc.target.getPc s) mc.ffiEntryPcs 0 = some index)
    (hname : holEl index mc.ffiNames = .sharedMem .mappedRead)
    (nb : BitVec 8) (r : Nat) (off : BitVec w) (reg : Nat) (rpc : BitVec w)
    (hlookup : sptAListLookup index mc.mmioInfo = some (nb, .addr r off, reg, rpc))
    (hcond : (if nb = 0 then (mc.target.getReg s r + off).toNat % (w / 8) = 0 else True) ∧
                    mc.sharedAddresses (mc.target.getReg s r + off) ∧
                    isValidMappedRead (mc.target.getPc s) nb (.addr r off) reg rpc mc.target s
                      mc.progAddresses)
    (newFfi : HolFfiState σ) (newBytes : List (BitVec 8))
    (hcall : callFFIHOL ffi (holEl index mc.ffiNames) [nb]
      (HolByte.wordToBytes (mc.target.getReg s r + off) false) = .ret newFfi newBytes) :
    evaluateTargetHOL mc ffi (j + 1) s =
      evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } newFfi j
        (mc.ffiInterfer 0 (index, newBytes, s)) := by
  rw [evaluateTargetHOL]
  simp only [applyOracleHOL]
  rw [if_neg hA, if_neg hH, if_neg hC]
  simp only [hfi, hname, hlookup]
  rw [if_pos hcond, ← hname, hcall]

theorem eval_ffi_write_eq (mc : MachineConfig w S P) (ffi : HolFfiState σ) (j : Nat) (s : S)
    (hA : ¬ (mc.progAddresses (mc.target.getPc s) ∧ mc.target.getPc s ∉ mc.ffiEntryPcs))
    (hH : mc.target.getPc s ≠ mc.haltPc) (hC : mc.target.getPc s ≠ mc.ccachePc)
    (index : Nat) (hfi : Misc.findIndex (mc.target.getPc s) mc.ffiEntryPcs 0 = some index)
    (hname : holEl index mc.ffiNames = .sharedMem .mappedWrite)
    (nb : BitVec 8) (r : Nat) (off : BitVec w) (reg : Nat) (rpc : BitVec w)
    (hlookup : sptAListLookup index mc.mmioInfo = some (nb, .addr r off, reg, rpc))
    (hcond : (if nb = 0 then (mc.target.getReg s r + off).toNat % (w / 8) = 0 else True) ∧
                    mc.sharedAddresses (mc.target.getReg s r + off) ∧
                    isValidMappedWrite (mc.target.getPc s) nb (.addr r off) reg rpc mc.target s
                      mc.progAddresses)
    (newFfi : HolFfiState σ) (newBytes : List (BitVec 8))
    (hcall : callFFIHOL ffi (holEl index mc.ffiNames) [nb]
      ((if nb = 0 then HolByte.wordToBytes (mc.target.getReg s reg) false
          else HolByte.wordToBytesAux nb.toNat (mc.target.getReg s reg) false) ++
        HolByte.wordToBytes (mc.target.getReg s r + off) false) = .ret newFfi newBytes) :
    evaluateTargetHOL mc ffi (j + 1) s =
      evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } newFfi j
        (mc.ffiInterfer 0 (index, newBytes, s)) := by
  rw [evaluateTargetHOL]
  simp only [applyOracleHOL]
  rw [if_neg hA, if_neg hH, if_neg hC]
  simp only [hfi, hname, hlookup]
  rw [if_pos hcond, ← hname, hcall]

end Unfold

/-- Discharge `SimConfig` for the oracle-shifted configurations produced by one
evaluator step. -/
macro "simcfg " h:term : tactic => `(tactic| (constructor <;> first
  | rfl
  | exact ($h).ptr2Reg | exact ($h).len2Reg | exact ($h).ptrReg | exact ($h).lenReg
  | exact ($h).progAddresses | exact ($h).sharedAddresses | exact ($h).ffiEntryPcs
  | exact ($h).ffiNames | exact ($h).haltPc | exact ($h).ccachePc | exact ($h).mmioInfo
  | exact ($h).config | exact ($h).getPc | exact ($h).getReg | exact ($h).getByte
  | exact ($h).stateOk | exact ($h).next
  | exact fun n => ($h).nextInterfer (n + 1) | exact ($h).nextInterfer
  | exact fun n => ($h).ffiInterfer (n + 1) | exact ($h).ffiInterfer
  | exact fun n => ($h).ccacheInterfer (n + 1) | exact ($h).ccacheInterfer))

/-! ## The simulation theorem -/


theorem ite_pos' {c : Prop} {inst : Decidable c} (hc : c) {α : Sort _} (a b : α) :
    @ite α c inst a b = a := by simp [hc]
theorem ite_neg' {c : Prop} {inst : Decidable c} (hc : ¬c) {α : Sort _} (a b : α) :
    @ite α c inst a b = b := by simp [hc]

theorem corr_ite {R : S1 → S2 → Prop} {c1 c2 : Prop} {i1 : Decidable c1} {i2 : Decidable c2}
    {a1 b1 : MachineResult × S1 × HolFfiState σ} {a2 b2 : MachineResult × S2 × HolFfiState σ}
    (hiff : c1 ↔ c2) (hpos : c1 → c2 → ResultCorr R a1 a2)
    (hneg : ¬c1 → ¬c2 → ResultCorr R b1 b2) :
    ResultCorr R (@ite _ c1 i1 a1 b1) (@ite _ c2 i2 a2 b2) := by
  by_cases h : c1
  · have h2 := hiff.mp h
    simp only [h, h2, ite_true]; exact hpos h h2
  · have h2 : ¬c2 := fun h2 => h (hiff.mpr h2)
    simp only [h, h2, ite_false]; exact hneg h h2

theorem evaluate_sim {R : S1 → S2 → Prop} {Safe : S1 → Prop} :
    ∀ (k : Nat) (mc1 : MachineConfig w S1 P1) (mc2 : MachineConfig w S2 P2)
      (ffi : HolFfiState σ) (s1 : S1) (s2 : S2),
    SimConfig mc1 mc2 R Safe → R s1 s2 → RunSafeUpTo mc1 ffi Safe k s1 →
    ResultCorr R (evaluateTargetHOL mc1 ffi k s1) (evaluateTargetHOL mc2 ffi k s2)
  | 0, _, _, _, _, _, _, hr, _ => ⟨rfl, rfl, hr⟩
  | k + 1, mc1, mc2, ffi, s1, s2, h, hr, hsafe => by
    have ih := evaluate_sim (R := R) (Safe := Safe) k
    have hpc := h.getPc s1 s2 hr
    have hbyte := h.getByte s1 s2 hr
    have hreg := h.getReg s1 s2 hr
    have hok := h.stateOk s1 s2 hr
    simp only [evaluateTargetHOL, applyOracleHOL]
    rw [← hpc, ← hbyte, ← hreg, ← hok, ← h.progAddresses, ← h.ffiEntryPcs, ← h.config,
      ← h.haltPc, ← h.ccachePc, ← h.ptrReg, ← h.lenReg, ← h.ffiNames, ← h.mmioInfo,
      ← h.sharedAddresses, ← readFfiBytearrays_congr h hr]
    generalize hpcv : mc1.target.getPc s1 = pc
    by_cases hA : mc1.progAddresses pc ∧ pc ∉ mc1.ffiEntryPcs
    · rw [ite_pos' hA, ite_pos' hA]
      by_cases hB : encodedBytesInMemHOL mc1.target.config pc (mc1.target.getByte s1) mc1.progAddresses
      · rw [ite_pos' hB, ite_pos' hB]
        by_cases hS : mc1.target.stateOk s1 = true
        · have hg : StepGuard mc1 s1 := ⟨hS, hpcv ▸ hA.1, hpcv ▸ hA.2, hpcv ▸ hB⟩
          have hsafe1 : Safe s1 := hsafe 0 (by omega) s1 ffi rfl hg
          have hR1 := h.next s1 s2 hr hg hsafe1
          have hR2 := h.nextInterfer 0 _ _ hR1
          have hiff : (mc1.target.stateOk s1 = true ∧
              mc1.target.stateOk (mc1.target.next s1) = true ∧
                mc1.target.stateOk (mc1.nextInterfer 0 (mc1.target.next s1)) = true ∧
                  ∀ (x : BitVec w),
                    ¬mc1.progAddresses x →
                      mc1.target.getByte (mc1.target.next s1) x = mc1.target.getByte s1 x) ↔
              (mc1.target.stateOk s1 = true ∧
              mc2.target.stateOk (mc2.target.next s2) = true ∧
                mc2.target.stateOk (mc2.nextInterfer 0 (mc2.target.next s2)) = true ∧
                  ∀ (x : BitVec w),
                    ¬mc1.progAddresses x →
                      mc2.target.getByte (mc2.target.next s2) x = mc1.target.getByte s1 x) := by
            rw [h.stateOk _ _ hR1, h.stateOk _ _ hR2, h.getByte _ _ hR1]
          refine corr_ite hiff (fun hC _ => ?_) (fun _ _ => ⟨rfl, rfl, hr⟩)
          refine ih _ _ _ _ _ ?_ hR2 ?_
          · simcfg h
          · subst hpcv
            exact RunSafeUpTo.tail (mc := mc1) (ffi := ffi) (s := s1) (fun _ ht => ht)
              (fun j => eval_next_eq mc1 ffi j s1 hA hB hC) hsafe
        · refine corr_ite ?_ (fun h' _ => absurd h'.1 hS) (fun _ _ => ⟨rfl, rfl, hr⟩)
          constructor
          · intro h'; exact absurd h'.1 hS
          · intro h'; exact absurd h'.1 hS
      · rw [ite_neg' hB, ite_neg' hB]
        exact ⟨rfl, rfl, hr⟩
    · rw [ite_neg' hA, ite_neg' hA]
      refine corr_ite Iff.rfl (fun _ _ => ⟨rfl, rfl, hr⟩) (fun hH _ => ?_)
      refine corr_ite Iff.rfl (fun hC _ => ?_) (fun hC _ => ?_)
      · refine ih _ _ _ _ _ ?_ (h.ccacheInterfer 0 _ _ _ _ hr) ?_
        · simcfg h
        · subst hpcv
          exact RunSafeUpTo.tail (mc := mc1) (ffi := ffi) (s := s1) (fun _ ht => ht)
            (fun j => eval_ccache_eq mc1 ffi j s1 hA hH hC) hsafe
      · rcases hfi : Misc.findIndex pc mc1.ffiEntryPcs 0 with _ | index
        · exact ⟨rfl, rfl, hr⟩
        dsimp only
        split
        · rename_i op hname
          simp only [hname]
          rcases hl : sptAListLookup index mc1.mmioInfo with _ | ⟨nb, ⟨r, off⟩, reg, rpc⟩
          · exact ⟨rfl, rfl, hr⟩
          dsimp only
          cases op
          · refine corr_ite ?_ (fun hcond _ => ?_) (fun _ _ => ⟨rfl, rfl, hr⟩)
            · rw [isValidMappedRead_congr mc1.target mc2.target s1 s2 _ _ _ _ _ _ h.config hbyte]
            rcases hc : callFFIHOL ffi (HolFfiName.sharedMem HolShmemOp.mappedRead) [nb]
                (HolByte.wordToBytes (mc1.target.getReg s1 r + off) false) with
              ⟨newFfi, newBytes⟩ | ev
            · refine ih _ _ _ _ _ ?_ (h.ffiInterfer 0 _ _ _ _ hr) ?_
              · simcfg h
              · subst hpcv
                exact RunSafeUpTo.tail (mc := mc1) (ffi := ffi) (s := s1) (fun _ ht => ht)
                  (fun j => eval_ffi_read_eq mc1 ffi j s1 hA hH hC index hfi hname nb r off reg rpc
                    hl hcond newFfi newBytes (by rw [hname]; exact hc)) hsafe
            · exact ⟨rfl, rfl, hr⟩
          · refine corr_ite ?_ (fun hcond _ => ?_) (fun _ _ => ⟨rfl, rfl, hr⟩)
            · rw [isValidMappedWrite_congr mc1.target mc2.target s1 s2 _ _ _ _ _ _ h.config hbyte]
            rcases hc : callFFIHOL ffi (HolFfiName.sharedMem HolShmemOp.mappedWrite) [nb]
                ((if nb = 0 then HolByte.wordToBytes (mc1.target.getReg s1 reg) false
                    else HolByte.wordToBytesAux nb.toNat (mc1.target.getReg s1 reg) false) ++
                  HolByte.wordToBytes (mc1.target.getReg s1 r + off) false) with
              ⟨newFfi, newBytes⟩ | ev
            · refine ih _ _ _ _ _ ?_ (h.ffiInterfer 0 _ _ _ _ hr) ?_
              · simcfg h
              · subst hpcv
                exact RunSafeUpTo.tail (mc := mc1) (ffi := ffi) (s := s1) (fun _ ht => ht)
                  (fun j => eval_ffi_write_eq mc1 ffi j s1 hA hH hC index hfi hname nb r off reg rpc
                    hl hcond newFfi newBytes (by rw [hname]; exact hc)) hsafe
            · exact ⟨rfl, rfl, hr⟩
        · rename_i name hname
          simp only [hname]
          rcases hl : sptAListLookup index mc1.mmioInfo with _ | x
          · dsimp only
            rcases hread : readFfiBytearraysHOL mc1 s1 with ⟨_ | b1, _ | b2⟩
            · exact ⟨rfl, rfl, hr⟩
            · exact ⟨rfl, rfl, hr⟩
            · exact ⟨rfl, rfl, hr⟩
            dsimp only
            rcases hc : callFFIHOL ffi (HolFfiName.extCall name) b1 b2 with ⟨newFfi, newBytes⟩ | ev
            · refine ih _ _ _ _ _ ?_ (h.ffiInterfer 0 _ _ _ _ hr) ?_
              · simcfg h
              · subst hpcv
                exact RunSafeUpTo.tail (mc := mc1) (ffi := ffi) (s := s1) (fun _ ht => ht)
                  (fun j => eval_ffi_ext_eq mc1 ffi j s1 hA hH hC index hfi name hname hl b1 b2 hread
                    newFfi newBytes (by rw [hname]; exact hc)) hsafe
            · exact ⟨rfl, rfl, hr⟩
          · exact ⟨rfl, rfl, hr⟩

/-- **Generic behaviour equivalence.** Under `SimConfig` and a related initial
state, if every guarded step of the first machine's run is `Safe`, the two
machines have exactly the same `machineSemHOL` behaviours (termination outcome,
I/O trace, divergence trace and failure). -/
theorem machineSem_sim {R : S1 → S2 → Prop} {Safe : S1 → Prop}
    {mc1 : MachineConfig w S1 P1} {mc2 : MachineConfig w S2 P2} {ffi : HolFfiState σ}
    {s1 : S1} {s2 : S2} (h : SimConfig mc1 mc2 R Safe) (hr : R s1 s2)
    (hsafe : RunSafe mc1 ffi Safe s1) (b : HolBehaviour) :
    machineSemHOL mc1 ffi s1 b ↔ machineSemHOL mc2 ffi s2 b := by
  have hc : ∀ k, ResultCorr R (evaluateTargetHOL mc1 ffi k s1) (evaluateTargetHOL mc2 ffi k s2) :=
    fun k => evaluate_sim k mc1 mc2 ffi s1 s2 h hr (hsafe k)
  have hres : ∀ k, (evaluateTargetHOL mc1 ffi k s1).1 = (evaluateTargetHOL mc2 ffi k s2).1 :=
    fun k => (hc k).1
  have hffi : ∀ k, (evaluateTargetHOL mc1 ffi k s1).2.2 = (evaluateTargetHOL mc2 ffi k s2).2.2 :=
    fun k => (hc k).2.1
  have triple : ∀ {S : Type} (t : MachineResult × S × HolFfiState σ) (r : MachineResult),
      (∃ ms' f', t = (r, ms', f')) ↔ t.1 = r := by
    intro S t r
    constructor
    · rintro ⟨ms', f', rfl⟩; rfl
    · intro e; exact ⟨t.2.1, t.2.2, by rw [← e]⟩
  cases b with
  | terminate outcome events =>
    simp only [machineSemHOL]
    constructor
    · rintro ⟨k, ms', f', he, hev⟩
      refine ⟨k, (evaluateTargetHOL mc2 ffi k s2).2.1, f', ?_, hev⟩
      have e1 := congrArg Prod.fst he
      have e3 := congrArg (fun t => t.2.2) he
      simp only at e1 e3
      rw [hres k] at e1; rw [hffi k] at e3
      rw [← e1, ← e3]
    · rintro ⟨k, ms', f', he, hev⟩
      refine ⟨k, (evaluateTargetHOL mc1 ffi k s1).2.1, f', ?_, hev⟩
      have e1 := congrArg Prod.fst he
      have e3 := congrArg (fun t => t.2.2) he
      simp only at e1 e3
      rw [← hres k] at e1; rw [← hffi k] at e3
      rw [← e1, ← e3]
  | diverge trace =>
    simp only [machineSemHOL]
    have hset : (fun ll => ∃ k : Nat,
          HolLList.fromList (evaluateTargetHOL mc1 ffi k s1).2.2.ioEvents = ll) =
        (fun ll => ∃ k : Nat,
          HolLList.fromList (evaluateTargetHOL mc2 ffi k s2).2.2.ioEvents = ll) := by
      funext ll; simp only [hffi]
    rw [hset]
    have htime : (∀ k, ∃ ms' ffi', evaluateTargetHOL mc1 ffi k s1 = (.timeOut, ms', ffi')) ↔
        (∀ k, ∃ ms' ffi', evaluateTargetHOL mc2 ffi k s2 = (.timeOut, ms', ffi')) := by
      simp only [triple, hres]
    rw [htime]
  | fail =>
    simp only [machineSemHOL, hres]

end

end RiscvImCompare

