module

public import BinaryPairBound.MainProof
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
@[expose] public section

namespace BinaryPairBound

/-- A binary joint probability law, with four actual nonnegative atom masses. -/
structure BinaryLaw where
  mass : Bool → Bool → ℝ
  nonneg : ∀ a b, 0 ≤ mass a b
  total : mass false false + mass false true + mass true false + mass true true = 1

namespace BinaryLaw

def input (P : BinaryLaw) : ℝ := P.mass true false + P.mass true true
def output (P : BinaryLaw) : ℝ := P.mass false true + P.mass true true
/-- Conditional probabilities; the value on a zero-probability conditioning event is zero. -/
def left (P : BinaryLaw) : ℝ := P.mass false true / (1 - P.input)
def right (P : BinaryLaw) : ℝ := P.mass true false / P.input

def entropy (P : BinaryLaw) : ℝ :=
  Real.negMulLog (P.mass false false) + Real.negMulLog (P.mass false true) +
    Real.negMulLog (P.mass true false) + Real.negMulLog (P.mass true true)
/-- Shannon mutual information in nats: entropy of each marginal minus joint entropy. -/
def mutualInfo (P : BinaryLaw) : ℝ := H P.input + H P.output - P.entropy
/-- The distribution-dependent KL contraction coefficient, using its Bernoulli parametrization. -/
def contraction (P : BinaryLaw) : ℝ := S P.input P.left P.right

def IsIndependent (P : BinaryLaw) : Prop :=
  ∀ a b, P.mass a b = (P.mass a false + P.mass a true) *
    (P.mass false b + P.mass true b)
/-- A doubly symmetric binary law, including noiseless and complemented sources. -/
def IsDSBS (P : BinaryLaw) : Prop :=
  P.mass false false = P.mass true true ∧ P.mass false true = P.mass true false

lemma input_mem (P : BinaryLaw) : P.input ∈ Set.Icc (0 : ℝ) 1 := by
  have h00 := P.nonneg false false
  have h01 := P.nonneg false true
  have h10 := P.nonneg true false
  have h11 := P.nonneg true true
  have ht := P.total
  unfold input
  constructor <;> linarith

lemma output_mem (P : BinaryLaw) : P.output ∈ Set.Icc (0 : ℝ) 1 := by
  have h00 := P.nonneg false false
  have h01 := P.nonneg false true
  have h10 := P.nonneg true false
  have h11 := P.nonneg true true
  have ht := P.total
  unfold output
  constructor <;> linarith

lemma valid (P : BinaryLaw) : Valid P.input P.left P.right := by
  have hs := P.input_mem
  have h00 := P.nonneg false false
  have h01 := P.nonneg false true
  have h10 := P.nonneg true false
  have h11 := P.nonneg true true
  have ht := P.total
  refine ⟨hs, ⟨div_nonneg h01 (sub_nonneg.mpr hs.2), ?_⟩, ⟨div_nonneg h10 hs.1, ?_⟩⟩
  · unfold left
    by_cases h : P.input = 1
    · simp [h]
    · apply (div_le_one (by have := hs.2; positivity : 0 < 1 - P.input)).mpr
      unfold input
      linarith
  · unfold right
    by_cases h : P.input = 0
    · simp [h]
    · apply (div_le_one (lt_of_le_of_ne hs.1 (Ne.symm h))).mpr
      unfold input
      linarith

lemma mass01 (P : BinaryLaw) : P.mass false true = (1 - P.input) * P.left := by
  unfold left
  by_cases h : 1 - P.input = 0
  · have ht := P.total
    have h00 := P.nonneg false false
    have h01 := P.nonneg false true
    have hsum := h
    unfold input at hsum
    rw [h, zero_mul]
    linarith
  · field_simp

lemma mass10 (P : BinaryLaw) : P.mass true false = P.input * P.right := by
  unfold right
  by_cases h : P.input = 0
  · have h10 := P.nonneg true false
    have h11 := P.nonneg true true
    have hsum := h
    unfold input at hsum
    simp only [h, zero_mul]
    linarith
  · field_simp

lemma mass00 (P : BinaryLaw) : P.mass false false = (1 - P.input) * (1 - P.left) := by
  have ht := P.total
  have hm := P.mass01
  unfold input at hm ⊢
  nlinarith

lemma mass11 (P : BinaryLaw) : P.mass true true = P.input * (1 - P.right) := by
  have hm := P.mass10
  unfold input at hm ⊢
  nlinarith

lemma output_eq (P : BinaryLaw) : P.output = q P.left P.right P.input := by
  unfold output q k
  rw [P.mass01, P.mass11]
  ring

lemma entropy_eq (P : BinaryLaw) :
    P.entropy = H P.input + (1 - P.input) * H P.left + P.input * H P.right := by
  unfold entropy
  rw [P.mass00, P.mass01, P.mass10, P.mass11]
  simp only [Real.negMulLog_mul, H, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

lemma mutualInfo_eq (P : BinaryLaw) : P.mutualInfo = J P.input P.left P.right := by
  rw [mutualInfo, P.entropy_eq, P.output_eq]
  unfold J
  ring

lemma independent_iff (P : BinaryLaw) :
    P.IsIndependent ↔ Independent P.input P.left P.right := by
  have h00 := P.mass00
  have h01 := P.mass01
  have h10 := P.mass10
  have h11 := P.mass11
  constructor
  · intro h
    have h' := h true true
    simp only [h01, h10, h11] at h'
    unfold Independent
    by_cases hs0 : P.input = 0
    · exact Or.inl hs0
    by_cases hs1 : P.input = 1
    · exact Or.inr (Or.inl hs1)
    right; right
    have he : P.input * (1 - P.input) * (1 - P.left - P.right) = 0 := by nlinarith [h']
    have he' : 1 - P.left - P.right = 0 :=
      (mul_eq_zero.mp he).resolve_left (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1)))
    linarith
  · intro h a b
    rcases h with h | h | h <;> cases a <;> cases b
    all_goals simp only [h00, h01, h10, h11]
    all_goals first | simp [h] | (rw [show P.right = 1 - P.left by linarith]; ring)

lemma dsbs_iff (P : BinaryLaw) : P.IsDSBS ↔ DSBS P.input P.left P.right := by
  constructor
  · rintro ⟨h00, h01⟩
    have ht := P.total
    have hs : P.input = 1 / 2 := by unfold input; linarith
    refine ⟨hs, ?_⟩
    unfold left right
    rw [hs, h01]
    norm_num
  · rintro ⟨hs, hcd⟩
    constructor
    · rw [P.mass00, P.mass11, hs, hcd]
      ring
    · rw [P.mass01, P.mass10, hs, hcd]
      ring

/-- The sharp bound for an arbitrary binary joint law. -/
theorem sharp_bound (P : BinaryLaw) : P.mutualInfo ≤ phi P.contraction := by
  rw [P.mutualInfo_eq]
  exact BinaryPairBound.sharp_bound P.valid

/-- Equality is exactly product joint law or a doubly symmetric joint law. -/
theorem sharp_equality_iff (P : BinaryLaw) :
    P.mutualInfo = phi P.contraction ↔ P.IsIndependent ∨ P.IsDSBS := by
  rw [P.mutualInfo_eq, contraction, BinaryPairBound.sharp_equality_iff P.valid,
    P.independent_iff, P.dsbs_iff]

end BinaryLaw
end BinaryPairBound
