module

import BinaryPairBound

/-!
Guarded axiom checks for the verified milestones. These reject sorryAx or
additional axioms. A conditional theorem still has its explicit premises:
mainTheorem_of_maximizersMerge is NOT an inhabitant of MainTheorem.
-/

/-- info: 'BinaryPairBound.equation_4_1_log_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.equation_4_1_log_ratio

/-- info: 'BinaryPairBound.D_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.D_pos

/-- info: 'BinaryPairBound.D_dataProcessing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.D_dataProcessing

/-- info: 'BinaryPairBound.S_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_mem_Icc

/-- info: 'BinaryPairBound.S_le_iff_supporting_tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_le_iff_supporting_tangent

/-- info: 'BinaryPairBound.J_eq_zero_iff_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.J_eq_zero_iff_independent

/-- info: 'BinaryPairBound.J_eq_log_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.J_eq_log_two_iff

/-- info: 'BinaryPairBound.S_eq_zero_iff_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_eq_zero_iff_independent

/-- info: 'BinaryPairBound.S_output_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_output_flip

/-- info: 'BinaryPairBound.S_simultaneous_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_simultaneous_flip

/-- info: 'BinaryPairBound.deriv2_entropyCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.deriv2_entropyCurve

/-- info: 'BinaryPairBound.rhoSquared_eq_eta_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.rhoSquared_eq_eta_iff

/-- info: 'BinaryPairBound.convexOn_posteriorEntropyCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.convexOn_posteriorEntropyCurve

/-- info: 'BinaryPairBound.phi_increment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.phi_increment_le

/-- info: 'BinaryPairBound.phi_increment_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.phi_increment_eq_iff

/-- info: 'BinaryPairBound.J_le_phi_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.J_le_phi_eta

/-- info: 'BinaryPairBound.merging_eq_iff_dsbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.merging_eq_iff_dsbs

/-- info: 'BinaryPairBound.S_le_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_le_eta

/-- info: 'BinaryPairBound.rhoSquared_le_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.rhoSquared_le_S

/-- info: 'BinaryPairBound.S_distinguishedInput_eq_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_distinguishedInput_eq_eta

/-- info: 'BinaryPairBound.merging_sharp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.merging_sharp_bound

/-- info: 'BinaryPairBound.merging_sharp_eq_iff_dsbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.merging_sharp_eq_iff_dsbs

/-- info: 'BinaryPairBound.S_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.S_symmetric

/-- info: 'BinaryPairBound.sharp_equality_of_independent_or_dsbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.sharp_equality_of_independent_or_dsbs

/-- info: 'BinaryPairBound.exists_sharp_cap_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.exists_sharp_cap_witness

/-- info: 'BinaryPairBound.exists_cap_maximizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.exists_cap_maximizer

/-- info: 'BinaryPairBound.exists_nontrivial_normalized_maximizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.exists_nontrivial_normalized_maximizer

/-- info: 'BinaryPairBound.hasDerivAt_contactGap_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.hasDerivAt_contactGap_r

/-- info: 'BinaryPairBound.hasDerivAt_contactGap_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.hasDerivAt_contactGap_q

/-- info: 'BinaryPairBound.contactGap_implicit_slope_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.contactGap_implicit_slope_s

/-- info: 'BinaryPairBound.contactGap_implicit_slope_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.contactGap_implicit_slope_q

/-- info: 'BinaryPairBound.sharpBound_iff_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.sharpBound_iff_normalized

/-- info: 'BinaryPairBound.mainTheorem_of_maximizersMerge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.mainTheorem_of_maximizersMerge

-- Deliberately display the remaining premise in the verification output.
#check (BinaryPairBound.mainTheorem_of_maximizersMerge :
  BinaryPairBound.MaximizersMerge → BinaryPairBound.MainTheorem)
#print axioms BinaryPairBound.mainTheorem_of_maximizersMerge
#check BinaryPairBound.SharpBound
#check BinaryPairBound.EqualityClassification
