module

public import BinaryPairBound.RandomVariables
public import BinaryPairBound.ReverseChannel

/-! # The Section 10 two-direction conclusion for actual random variables -/
noncomputable section
@[expose] public section

namespace BinaryPairBound
namespace BinaryLaw

theorem ext_mass {P Q : BinaryLaw} (h : P.mass = Q.mass) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- Swap the coordinates of the actual joint probability table. -/
def swap (P : BinaryLaw) : BinaryLaw where
  mass a b := P.mass b a
  nonneg a b := P.nonneg b a
  total := by have h := P.total; linarith

lemma swap_input (P : BinaryLaw) : P.swap.input = P.output := rfl

lemma swap_left (P : BinaryLaw) : P.swap.left = reverseC P.input P.left P.right := by
  unfold left swap reverseC
  change P.mass true false / (1 - P.output) = _
  rw [P.output_eq, P.mass10]
  rfl

lemma swap_right (P : BinaryLaw) : P.swap.right = reverseD P.input P.left P.right := by
  unfold right swap reverseD
  change P.mass false true / P.output = _
  rw [P.output_eq, P.mass01]
  rfl

lemma swap_contraction (P : BinaryLaw) :
    P.swap.contraction = reverseS P.input P.left P.right := by
  rw [contraction, swap_input, swap_left, swap_right, P.output_eq]
  rfl

/-- The same sharp bound applied in both directions. -/
theorem bidirectional_bound (P : BinaryLaw) :
    P.mutualInfo ≤ phi (min P.contraction P.swap.contraction) := by
  rw [P.mutualInfo_eq, P.swap_contraction]
  exact BinaryPairBound.bidirectional_bound P.valid

/-- Unequal directed coefficients force strictness. -/
theorem bidirectional_strict (P : BinaryLaw) (hne : P.contraction ≠ P.swap.contraction) :
    P.mutualInfo < phi (min P.contraction P.swap.contraction) := by
  rw [P.mutualInfo_eq, P.swap_contraction]
  rw [P.swap_contraction] at hne
  exact BinaryPairBound.bidirectional_strict_of_ne P.valid hne

end BinaryLaw

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma binaryLaw_swap (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) :
    binaryLaw μ Z W hZ hW = (binaryLaw μ W Z hW hZ).swap := by
  apply BinaryLaw.ext_mass
  funext a b
  simp only [binaryLaw, BinaryLaw.swap, Set.inter_comm]

/-- Section 10's minimum bound, using the coefficient of each actual variable order. -/
theorem binary_random_variable_bidirectional_bound (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ ≤
      phi (min (binaryContraction μ W Z hW hZ) (binaryContraction μ Z W hZ hW)) := by
  unfold binaryMutualInfo binaryContraction
  rw [binaryLaw_swap]
  exact BinaryLaw.bidirectional_bound _

/-- Section 10's nonattainment assertion for unequal directed coefficients. -/
theorem binary_random_variable_bidirectional_strict (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z)
    (hne : binaryContraction μ W Z hW hZ ≠ binaryContraction μ Z W hZ hW) :
    binaryMutualInfo μ W Z hW hZ <
      phi (min (binaryContraction μ W Z hW hZ) (binaryContraction μ Z W hZ hW)) := by
  unfold binaryMutualInfo binaryContraction at *
  rw [binaryLaw_swap] at hne ⊢
  exact BinaryLaw.bidirectional_strict _ hne

end BinaryPairBound
