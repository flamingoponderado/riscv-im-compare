# riscv-im-compare

A Lean 4 development comparing two RISC-V semantics:

| | Model | Where |
|---|---|---|
| **L3** | Flapjack's L3-derived RV64IM model (`Flapjack.RiscV.L3`, step function `riscvNext`), which Flapjack's Pancake compiler-correctness theorem is stated over | `deps/flapjack`, branch `riscv-im` (pinned at `7981f765c`) |
| **zkvm** | riscv-zkvm's hand-written computable RV64IM model (`RiscvZkvm.Rv64`, step function `RiscvZkvm.Rv64.step`) | `deps/riscv-zkvm`, tag `v0.3.1` (pinned at `93ab6ef`) |

**Comparison criterion.** We do not compare instruction encodings or
irrelevant microarchitectural details; for example, it does not matter whether
`add x0, x0, x0` counts as a no-op or as an addition. What matters is the
**observable behaviour** of a compiled program, as Flapjack defines it in its
compiler-correctness theorem: `machineSemHOL`, a port of CakeML's
`machine_sem`. A behaviour consists of:
- the termination outcome together with the I/O (FFI) event trace;
- or, for a diverging run, the divergence trace;
- or failure.

The result is that Flapjack's Pancake → RISC-V correctness theorem carries
over to riscv-zkvm. This holds under explicit side conditions, which are listed
under "Differences" below.

## Main results

All theorems are fully proved: there is no `sorry`, `native_decide` or
`bv_decide`, and no extra axioms. Only `propext`, `Classical.choice` and
`Quot.sound` are used; `RiscvImCompare/Axioms.lean` prints the axiom audit at
build time.

1. **Pancake compiler correctness on riscv-zkvm.** This is
   `RiscvImCompare.panToTargetCompileSemanticsZkvm` in
   `RiscvImCompare/Main.lean`. It keeps every premise of Flapjack's
   `panToTargetCompileSemanticsRiscV` verbatim. Its conclusion is that every
   `machineSemHOL` behaviour of the compiled program, run on
   `zkvmConfig mc …` (Flapjack's machine configuration with riscv-zkvm as the
   processor), is a behaviour allowed for the Pancake source program, up to
   resource limits. On top of Flapjack's premises it adds three more:
   - `Rel C ms z`: the riscv-zkvm initial state `z` is related to the L3
     initial state `ms`. Such a `z` always exists: `zOfL3`/`rel_zOfL3` build
     one.
   - `OraclesCorr C mc …`: the riscv-zkvm environment oracles correspond to
     the L3 ones. These are the oracles that model FFI calls,
     `next_interfer` and the code cache.
   - `RunSafe mc ffi (SafeL3 C) ms`: every step that the L3 run executes is
     `SafeL3`. The "Differences" section explains what this means.

2. **Behaviour equivalence.** This is `RiscvImCompare.machineSem_l3_iff_zkvm`.
   Under the same three conditions, the L3 machine and the riscv-zkvm machine
   have exactly the same set of `machineSemHOL` behaviours:

   `machineSemHOL mc ffi ms b ↔ machineSemHOL (zkvmConfig mc nextI ffiI ccacheI) ffi z b`.

3. **Single-step simulation.** This is `RiscvImCompare.step_sim` in
   `RiscvImCompare/SimStep.lean`. Suppose the L3 state is ok, the bytes at the
   PC encode some `asm` instruction (exactly the case in which Flapjack's
   evaluator calls `next`), and the step is `SafeL3`. Then one L3 step and one
   riscv-zkvm step preserve `Rel`.

   This covers every instruction that Flapjack's RISC-V encoder can produce,
   for any `asm` input and not only for compiler output. The encoder emits 37
   instruction kinds (`riscvAst_supported`):
   - ALU and immediate: `ADDI ANDI ORI XORI LUI AUIPC ADD SUB AND OR XOR SLTU`
   - shifts: `SLL SRL SRA SLLI SRLI SRAI`
   - multiply and divide: `MUL MULHU DIV`
   - loads: `LD LWU LHU LBU`
   - stores: `SD SW SH SB`
   - branches: `BEQ BNE BLT BGE BLTU BGEU`
   - jumps: `JAL JALR`

   The proof covers all register fields and immediates, including `x0` as a
   destination, division by zero, signed-division overflow, the high-half
   multiply, shift-amount masking, and branch and jump offset scaling.

4. **Generic simulation theorem.** This is `RiscvImCompare.machineSem_sim` in
   `RiscvImCompare/Simulation.lean`. It is independent of RISC-V: it applies
   to any two machine configurations that `machineSemHOL` can run, possibly
   over different state types. If a state relation makes the observations
   agree and is preserved by `next` (on guarded, `Safe` steps) and by the
   oracles, then the two machines have the same behaviours.

5. **Instruction-level agreement lemmas.** These are the building blocks of
   the step simulation:
   - `decode_encode_toZ` (`ZDecode.lean`): riscv-zkvm's executable decoder
     decodes the L3 encoding of each of the 37 instruction kinds to the
     corresponding riscv-zkvm instruction.
   - `load_*` and `store_*` (`Memory.lean`): L3's byte memory and
     riscv-zkvm's doubleword memory agree on aligned loads and stores of every
     size.

### How the comparison is set up

- **`zkvmTarget`** (`Relation.lean`) packages `RiscvZkvm.Rv64.step` as a
  Flapjack `HolAsmTarget`, so that Flapjack's own `machineSemHOL` can run on
  riscv-zkvm states.
  - A `ZState` is a riscv-zkvm `MachineState` plus an `ok` flag, which is
    cleared when `step` traps (returns `none`).
  - `stateOk` holds when the state has not trapped and the PC is 4-aligned.
    This mirrors L3's `riscvOk`, which also requires an aligned PC.
- **`Rel C ms z`** requires:
  - `riscvOk ms = zOk z`;
  - equal PCs;
  - equal raw register files;
  - riscv-zkvm's doubleword memory agrees with L3's byte memory at every
    8-aligned address;
  - on the instruction addresses `C` of the program, riscv-zkvm's fixed
    `code` map is riscv-zkvm's own `decode` of the instruction word stored in
    L3's memory.
- **`SafeL3 C ms`**, the condition on the L3 step about to execute, requires:
  - the PC is in `C`;
  - for loads and stores, the effective address passes riscv-zkvm's own
    validity check (alignment, and inside the memory map);
  - stores do not write any byte of an instruction in `C`.

## Differences between the two models

All of the following were found while building the proofs. Items 1–3 are
**real semantic differences** that the theorems carry as explicit
assumptions. Items 4–6 concern **what the two developments model**. Items 7–8
are **properties checked to agree**.

1. **Memory map and alignment (`RunSafe`, memory part).**
   - L3 executes every load and store at any address, misaligned accesses
     included. Misaligned accesses are handled by reading or writing across
     doublewords, and there is no access fault.
   - riscv-zkvm traps (`step` returns `none`) on misaligned accesses, and on
     any address outside its hard-coded zkVM memory map `isValidMemAddr`:
     `[0x20, 0x78000000] ∪ [0x40000000, 0x40002000] ∪ [0xa0000000, 0xc0000000]`.
     Address `0`, for example, is invalid.

   `Differences.lean` formalises this:
   - `l3_ld_total` and `l3_sd_total`: L3 always steps on `LD`/`SD`;
   - `zkvm_ld_traps` and `zkvm_sd_traps`: riscv-zkvm traps on an
     invalid/misaligned address;
   - `zkvm_address_zero_invalid`: address `0` is outside riscv-zkvm's memory
     map.

   Consequences:
   - Flapjack's theorem says nothing about where the compiled program's data
     lives. On riscv-zkvm, the heap, stack and globals must lie inside the
     zkVM memory map.
   - Whether compiled code only performs aligned accesses is not exported by
     Flapjack's top-level theorem. Even if Flapjack's backend proof
     establishes it internally (not checked here), it is an assumption in
     this development.

2. **Code is data in L3, not in riscv-zkvm (`RunSafe`, code part; `Rel.code`).**
   - L3 fetches the instruction bytes from memory at every step, so
     self-modifying code is possible.
   - riscv-zkvm executes from a separate, fixed `code : Word → Option Instr`
     map, which a loader fills in by decoding the image.

   The comparison therefore requires:
   - the executed PC lies in the program's instruction set `C`;
   - no store writes into `C`;
   - the environment oracles preserve the relation, and in particular do not
     rewrite code. This is part of `OraclesCorr`.

   Flapjack's evaluator itself permits writes inside `progAddresses`, which
   contains both code and data.

3. **Traps.**
   - riscv-zkvm `step` returns `none` on any trap. Here this is turned into a
     non-ok state, so Flapjack's evaluator reports `error`.
   - L3 `NextRISCV` returns `none` on an exception, and Flapjack's
     `riscvNext` is `holThe (NextRISCV s)`. The L3 successor of a trapping
     step is therefore an *unspecified* state, not a defined error.

   The two therefore cannot be compared on trapping steps. The proof shows
   that, for the 37 supported instructions and an ok state, L3 never raises
   an exception: jumps are always even-aligned, `in32BitMode` is false, and
   translation is bare. On `SafeL3` steps riscv-zkvm never traps either.

4. **Input/output and termination are modelled differently.**
   - In Flapjack (as in CakeML), I/O is an FFI call. The program jumps to an
     FFI entry PC; the evaluator then consults the FFI oracle, records an I/O
     event, and applies `ffiInterfer` to the machine state. Termination means
     jumping to `haltPc`, and the result is read from `ptrReg`.
   - riscv-zkvm has no FFI. I/O is done with `ECALL` syscalls:
     - `t0 = 0x10`: `write_output`;
     - `t0 = 0xF2`: `read_input`;
     - `t0 = 2`, `fd = 13`: `WRITE`.

     It halts on `ECALL` with `t0 = 0`, and it collects output in
     `publicValues`.

   In this development the riscv-zkvm processor is plugged into Flapjack's
   machine semantics. FFI calls, halting and the code cache are therefore
   handled by Flapjack's evaluator, with environment oracles over riscv-zkvm
   states (`OraclesCorr`).

   **Not done:** FFI stubs that implement Pancake's FFI calls with
   riscv-zkvm `ECALL`s, together with a proof that their effect on
   `publicValues`/`privateInput` matches an FFI oracle; and the connection
   between Flapjack's `haltPc` termination and riscv-zkvm's `ECALL` halt.
   Flapjack never emits `ECALL`, `EBREAK`, `FENCE` or `CSRS`, so none of
   riscv-zkvm's syscall, accelerator or trap semantics is exercised by
   compiled code.

5. **Instruction coverage.**
   - Flapjack's encoder emits only the 37 kinds listed above, and only 32-bit
     encodings: no compressed instructions and no `*W` word operations.
   - riscv-zkvm lacks the RV64 word-op family (`ADDW SUBW … REMUW`; see its
     `docs/validation.md`, known gap 2), but Flapjack never emits these.
   - L3 models further instructions, and riscv-zkvm models `SLT`, `SLTI`,
     `SLTIU`, `LW`, `LB`, `LH`, `MULH`, `MULHSU`, `DIVU`, `REM` and `REMU`.
     None of these is emitted, so they are not compared.

6. **State components not related.**
   - L3's CSRs, `Skip`, `NextFetch`, `log`, `ExitCode` and other bookkeeping
     state are not related, apart from the `riscvOk` conditions (`VM = 0`,
     `ArchBase = 2`, no pending control transfer or exception, aligned PC).
   - riscv-zkvm's `committed`, `publicValues`, `privateInput` and
     `inputBufBase` are left unconstrained. The 37 instructions do not touch
     them.
   - `getReg` in both targets reads the raw register file; reads of `x0` by
     instructions return 0 in both models.

7. **Agreement checked on every supported instruction.** Writes to `x0` are
   dropped in both models. Division by zero gives `-1` in both. Both use
   `BitVec.sdiv` for signed overflow. `MULHU` takes the high half of the
   128-bit product in both. Register shifts mask the shift amount to 6 bits.
   Branch and `JAL` offsets are stored as half-words in L3 and as bytes in
   riscv-zkvm, and agree. `JALR` clears bit 0 in both. `LUI`/`AUIPC`
   sign-extend from 32 bits in both. Loads zero-extend (`LWU`, `LHU`, `LBU`).
   Memory is little-endian in both.

8. **Decoder.** The relation uses riscv-zkvm's executable decoder
   `RiscvZkvm.Interpreter.decode`, which is what its ELF loader uses to fill
   `code`. Per riscv-zkvm's own known gap 3, that decoder is not tied to the
   Sail decoder.

### What is *not* proved

- **`RunSafe`.** It is not derived from Flapjack's compiler theorem. The
  facts it needs (aligned compiled accesses, stores staying out of the code)
  are not exported by `panToTargetCompileSemanticsRiscV`. Deriving them, if
  they hold, would mean re-entering Flapjack's backend proof.
- **`OraclesCorr`.** It is left to the instantiation, like the interference
  assumptions in Flapjack's theorem.
- **Sail.** There is no link to the Sail model. riscv-zkvm separately proves
  `RiscvZkvm.Rv64.step` against its Sail extraction (`RiscvZkvm.Rv64.SailEquiv`,
  under its own run invariants); composing the two results has not been
  attempted.
- **Flapjack's trust base.** The caveats in Flapjack's `docs/SOUNDNESS.md`
  apply unchanged; for example, the statement is about the logical compiler
  `compile_prog_max`.

## Layout

| File | Contents |
|---|---|
| `RiscvImCompare/Simulation.lean` | generic simulation theorem for `machineSemHOL` (`evaluate_sim`, `machineSem_sim`) |
| `RiscvImCompare/Defs.lean` | `toZ` (the 37 instructions → riscv-zkvm `Instr`), `l3Dword`, `l3Word`, `MemRel` |
| `RiscvImCompare/Image.lean` | every encoder output is supported; fetch inside the evaluator |
| `RiscvImCompare/ZDecode.lean` | riscv-zkvm `decode ∘ L3 Encode = toZ` |
| `RiscvImCompare/Memory.lean` | load and store agreement between byte and doubleword memories |
| `RiscvImCompare/Relation.lean` | `ZState`, `zkvmTarget`, `Rel`, `SafeL3` |
| `RiscvImCompare/L3Step.lean` | generic L3 `NextRISCV` equations |
| `RiscvImCompare/SimStep.lean` | per-instruction simulation and `step_sim` |
| `RiscvImCompare/Main.lean` | `zkvmConfig`, `machineSem_l3_iff_zkvm`, `panToTargetCompileSemanticsZkvm`, `zOfL3` |
| `RiscvImCompare/Differences.lean` | formalised memory-access differences |
| `RiscvImCompare/Axioms.lean` | axiom audit |

## Building

```sh
git submodule update --init      # deps/flapjack (riscv-im), deps/riscv-zkvm (v0.3.1)
lake exe cache get               # Mathlib cache (Flapjack depends on Mathlib)
lake build                       # builds the library and runs the axiom audit
```

- The toolchain is `leanprover/lean4:v4.33.1`, Flapjack's. riscv-zkvm v0.3.1
  pins v4.33.0 and is built from source with v4.33.1 without changes.
- A cold build compiles Flapjack (about 5,300 modules); this needs a lot of
  memory and CPU time.
- Use `lake build <Module>` rather than `lake env lean <file>`. With Lake's
  artifact cache enabled, the dependency `.olean`s are only materialised by
  `lake build`.

## License

MIT, © 2026 zkSecurity, see `LICENSE`. A theorem statement and a short proof
are adapted from Flapjack and remain under the BSD 3-Clause License; see
`LICENSE` and `LICENSES/flapjack-COPYRIGHT`.
