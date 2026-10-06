import RiscvImCompare.Main
import RiscvImCompare.ArbitraryCode

/-! Axiom audit of the main results (printed at build time). -/

#print axioms RiscvImCompare.machineSem_sim
#print axioms RiscvImCompare.step_sim
#print axioms RiscvImCompare.machineSem_l3_iff_zkvm
#print axioms RiscvImCompare.panToTargetCompileSemanticsZkvm
#print axioms RiscvImCompare.rel_zOfL3
#print axioms RiscvImCompare.step_sim_word
#print axioms RiscvImCompare.run_sim
#print axioms RiscvImCompare.l3_ecall_none
#print axioms RiscvImCompare.decode_eq_toZx
#print axioms RiscvImCompare.decode_some_toZx
#print axioms RiscvImCompare.Decode_toZx
#print axioms RiscvImCompare.run_sim_nonsystem
