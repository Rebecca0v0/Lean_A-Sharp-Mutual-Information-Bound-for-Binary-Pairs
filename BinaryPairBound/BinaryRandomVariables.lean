module

public import BinaryPairBound.MainTheorem
public import BinaryPairBound.FiniteInformation
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Binary probability laws and random-variable interfaces

把参数形式接到四格概率表和任意概率空间上的二元随机变量，并验证二元系数及AGKN特例的对应。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Four-cell binary laws and the scalar theorem

从四个联合概率恢复二元参数，并把主定理改写成二元联合分布的互信息结论。
-/

@[expose] public noncomputable section BinaryLaw

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

end BinaryLaw

/-! ## Equality of the finite coefficient and the binary parameter S

证明有限字母表系数在二元分布和二元信道上，恰好等于论文的 S(s,c,d)。
-/

@[expose] public noncomputable section BinaryKernel

open scoped BigOperators

namespace FiniteInfo

theorem Law.ext_mass {α : Type*} [Fintype α] {p q : Law α}
    (h : p.mass = q.mass) : p = q := by
  cases p; cases q; cases h; rfl

def bernoulli (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Law Bool where
  mass b := if b then s else 1 - s
  nonneg b := by cases b <;> simp [hs.1, sub_nonneg.mpr hs.2]
  total := by simp

def binaryChannel (c d : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) : Channel Bool Bool where
  prob a b := if a then (if b then 1 - d else d) else (if b then c else 1 - c)
  nonneg a b := by cases a <;> cases b <;> simp [hc.1, hd.1, sub_nonneg.mpr hc.2, sub_nonneg.mpr hd.2]
  total a := by cases a <;> simp

lemma out_binary {s c d : ℝ} (hv : Valid s c d) :
    out (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) =
      bernoulli (q c d s) (q_mem_Icc c d s hv.2.1 hv.2.2 hv.1) := by
  apply Law.ext_mass
  funext b
  cases b <;> simp [out, bernoulli, binaryChannel, q, k] <;> ring

def binaryMean (s : ℝ) (f : Bool → ℝ) : ℝ := (1 - s) * f false + s * f true

lemma sum_bernoulli {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (f : Bool → ℝ) :
    (∑ b, (bernoulli s hs).mass b * f b) = binaryMean s f := by
  simp [bernoulli, binaryMean, add_comm]

lemma binaryMean_nonneg {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {f : Bool → ℝ} (hf : ∀ b, 0 ≤ f b) : 0 ≤ binaryMean s f :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) (hf false)) (mul_nonneg hs.1 (hf true))

lemma binaryMean_transfer {s c d : ℝ} (hv : Valid s c d) (f : Bool → ℝ) :
    binaryMean (q c d s) (transfer (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) f) =
      binaryMean s f := by
  have h := sum_out_mul_transfer (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) f
  rw [out_binary hv, sum_bernoulli, sum_bernoulli] at h
  exact h

lemma bernoulli_entropy_formula {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (f : Bool → ℝ) (hf : ∀ b, 0 ≤ f b) (hm : 0 < binaryMean s f) :
    entropy (bernoulli s ⟨hs.1.le, hs.2.le⟩).mass f =
      binaryMean s f * D (s * f true / binaryMean s f) s := by
  change 0 < s ∧ s < 1 at hs
  have he := binary_mass_entropy (mul_nonneg (sub_nonneg.mpr hs.2.le) (hf false))
    (mul_nonneg hs.1.le (hf true))
  have hx : binaryMean s f * (s * f true / binaryMean s f) = s * f true := by field_simp
  rw [Real.negMulLog_mul, Real.negMulLog_mul] at he
  change binaryMean s f * H (s * f true / binaryMean s f) = _ at he
  simp only [Real.negMulLog_def] at he
  unfold entropy
  erw [sum_bernoulli]
  simp only [Fintype.sum_bool, bernoulli, Bool.false_eq_true, ↓reduceIte]
  unfold D
  have hxs := congrArg (fun z : ℝ => z * Real.log s) hx
  have hx1s := congrArg (fun z : ℝ => z * Real.log (1 - s)) hx
  unfold binaryMean at *
  nlinarith [he, hxs, hx1s]


lemma bernoulli_entropy_zero (f : Bool → ℝ) :
    entropy (bernoulli 0 (by norm_num)).mass f = 0 := by
  simp [entropy, bernoulli]

lemma bernoulli_entropy_one (f : Bool → ℝ) :
    entropy (bernoulli 1 (by norm_num)).mass f = 0 := by
  simp [entropy, bernoulli]

lemma normalized_input_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {f : Bool → ℝ} (hf : ∀ b, 0 ≤ f b) (hm : 0 < binaryMean s f) :
    s * f true / binaryMean s f ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (mul_nonneg hs.1 (hf true)) hm.le
  · apply (div_le_one hm).mpr
    have := mul_nonneg (sub_nonneg.mpr hs.2) (hf false)
    unfold binaryMean
    linarith

lemma normalized_output {s c d : ℝ} (hv : Valid s c d) (f : Bool → ℝ)
    (hm : 0 < binaryMean s f) :
    q c d s * transfer (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) f true /
      binaryMean s f = q c d (s * f true / binaryMean s f) := by
  change (0 ≤ s ∧ s ≤ 1) ∧ (0 ≤ c ∧ c ≤ 1) ∧ (0 ≤ d ∧ d ≤ 1) at hv
  have he := out_mul_transfer (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) f true
  rw [out_binary hv] at he
  simp only [bernoulli, binaryChannel, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true] at he
  erw [he]
  unfold q k binaryMean at *
  field_simp
  ring

lemma binary_entropy_transfer_formula {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) (f : Bool → ℝ) (hf : ∀ b, 0 ≤ f b)
    (hm : 0 < binaryMean s f) :
    entropy (out (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2)).mass
      (transfer (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) f) =
      binaryMean s f * D (q c d (s * f true / binaryMean s f)) (q c d s) := by
  rw [out_binary hv]
  rw [bernoulli_entropy_formula hn.2 _ (transfer_nonneg _ _ hf)
    (by rw [binaryMean_transfer hv]; exact hm)]
  rw [binaryMean_transfer hv, normalized_output hv f hm]

lemma contracts_binary_of_cap {lam s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) (hcap : KLCap lam s c d) :
    Contracts (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) lam := by
  intro f hf
  by_cases hz : binaryMean s f = 0
  · have hin := entropy_zero_of_mean_zero (bernoulli s hv.1) hf
      (by rw [sum_bernoulli]; exact hz)
    have hout := entropy_zero_of_mean_zero
      (out (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2))
      (transfer_nonneg _ _ hf)
      (by rw [sum_out_mul_transfer, sum_bernoulli]; exact hz)
    rw [hin, hout, mul_zero]
  · have hm : 0 < binaryMean s f := lt_of_le_of_ne (binaryMean_nonneg hv.1 hf) (Ne.symm hz)
    rw [binary_entropy_transfer_formula hv hn f hf hm]
    erw [bernoulli_entropy_formula hn.1 f hf hm]
    have h := mul_le_mul_of_nonneg_left
      (hcap _ (normalized_input_mem hv.1 hf hm)) hm.le
    nlinarith [h]

lemma cap_of_contracts_binary {lam s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d)
    (hcap : Contracts (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) lam) :
    KLCap lam s c d := by
  intro x hx
  let f : Bool → ℝ := fun b => if b then x / s else (1 - x) / (1 - s)
  have hf : ∀ b, 0 ≤ f b := by
    intro b; cases b
    · exact div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hn.1.2.le)
    · exact div_nonneg hx.1 hn.1.1.le
  have hm : binaryMean s f = 1 := by
    dsimp [binaryMean, f]
    field_simp [ne_of_gt hn.1.1, ne_of_gt (sub_pos.mpr hn.1.2)]
    ring
  have hmpos : 0 < binaryMean s f := by rw [hm]; norm_num
  have hx' : s * f true / binaryMean s f = x := by
    dsimp [f]
    rw [hm]
    field_simp [ne_of_gt hn.1.1]
  have h := hcap f hf
  rw [binary_entropy_transfer_formula hv hn f hf hmpos] at h
  erw [bernoulli_entropy_formula hn.1 f hf hmpos] at h
  erw [hx'] at h
  simpa only [hm, one_mul] using h

lemma contracts_binary_degenerate {lam s c d : ℝ} (hv : Valid s c d)
    (hn : ¬Nondegenerate s c d) (hlam : 0 ≤ lam) :
    Contracts (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) lam := by
  intro f hf
  have hdpi := entropy_transfer_le (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) hf
  by_cases hs0 : s = 0
  · subst s
    rw [bernoulli_entropy_zero] at hdpi ⊢
    simpa using hdpi
  by_cases hs1 : s = 1
  · subst s
    rw [bernoulli_entropy_one] at hdpi ⊢
    simpa using hdpi
  have hs : s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hv.1.1 (Ne.symm hs0), lt_of_le_of_ne hv.1.2 hs1⟩
  have hq := q_mem_Icc c d s hv.2.1 hv.2.2 hv.1
  have hqend : q c d s = 0 ∨ q c d s = 1 := by
    by_contra h
    push Not at h
    exact hn ⟨hs, lt_of_le_of_ne hq.1 (Ne.symm h.1), lt_of_le_of_ne hq.2 h.2⟩
  have hout : entropy (out (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2)).mass
      (transfer (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) f) = 0 := by
    rw [out_binary hv]
    rcases hqend with hq0 | hq1
    · simp only [hq0, bernoulli_entropy_zero]
    · simp only [hq1, bernoulli_entropy_one]
  rw [hout]
  exact mul_nonneg hlam (entropy_nonneg _ hf)

/-- The homogeneous finite-alphabet entropy cap is exactly the paper's KL cap,
including all deterministic input/output cases. -/
theorem contracts_binary_iff {lam s c d : ℝ} (hv : Valid s c d) (hlam : 0 ≤ lam) :
    Contracts (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) lam ↔ S s c d ≤ lam := by
  by_cases hn : Nondegenerate s c d
  · rw [S_le_iff_klCap hv hn]
    exact ⟨cap_of_contracts_binary hv hn, contracts_binary_of_cap hv hn⟩
  · rw [S_eq_zero_of_not_nondegenerate hn]
    exact ⟨fun _ => hlam, fun _ => contracts_binary_degenerate hv hn hlam⟩

/-- The finite-alphabet KL coefficient agrees with the original scalar supremum. -/
theorem coefficient_binary {s c d : ℝ} (hv : Valid s c d) :
    coefficient (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2) = S s c d := by
  apply le_antisymm
  · apply (coefficient_le_iff (S_nonneg hv)).mpr
    exact (contracts_binary_iff hv (S_nonneg hv)).mpr le_rfl
  · apply (contracts_binary_iff hv (coefficient_nonneg _ _)).mp
    exact contracts_coefficient _ _

end FiniteInfo

end BinaryKernel

/-! ## The full-support binary coefficient -/

@[expose] public noncomputable section AGKNBinary

namespace FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A non-deterministic Bernoulli input has full support on `Bool`. -/
theorem bernoulli_fullSupport {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hvalid : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ b, 0 < (bernoulli s hvalid).mass b := by
  intro b
  cases b <;> simp [bernoulli, hs.1, sub_pos.mpr hs.2]

/-- The direct AGKN coefficient is the paper's scalar `S` for binary laws.
The input is non-deterministic; the output is allowed to be deterministic. -/
theorem agknCoefficient_binary {s c d : ℝ} (hv : Valid s c d)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    agknCoefficient (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2)
      (bernoulli_fullSupport hs hv.1) = S s c d := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_binary hv

end FiniteInfo

end AGKNBinary

/-! ## Actual binary random variables on any probability space

从任意概率空间上的二元随机变量构造实际联合分布，并用通常的独立性陈述主定理。
-/

@[expose] public noncomputable section RandomVariables

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

private lemma real_bool_partition (X : Ω → Bool) (hX : Measurable X)
    (E : Set Ω) (hE : MeasurableSet E) :
    μ.real (E ∩ X ⁻¹' {false}) + μ.real (E ∩ X ⁻¹' {true}) = μ.real E := by
  rw [← measureReal_union]
  · congr 1
    ext ω
    cases h : X ω <;> simp [h]
  · apply Set.disjoint_left.mpr
    intro ω hf ht
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hf ht
    exact Bool.false_ne_true (hf.2.symm.trans ht.2)
  · exact hE.inter (hX (measurableSet_singleton true))

/-- The actual joint law of two binary random variables on any probability space. -/
def binaryLaw (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) : BinaryLaw where
  mass a b := μ.real (W ⁻¹' {a} ∩ Z ⁻¹' {b})
  nonneg _ _ := measureReal_nonneg
  total := by
    have h0 := real_bool_partition μ Z hZ (W ⁻¹' {false})
      (hW (measurableSet_singleton false))
    have h1 := real_bool_partition μ Z hZ (W ⁻¹' {true})
      (hW (measurableSet_singleton true))
    have ht := real_bool_partition μ W hW Set.univ MeasurableSet.univ
    simp only [Set.univ_inter, probReal_univ] at ht
    linarith

namespace binaryLaw

variable {μ} {W Z : Ω → Bool} (hW : Measurable W) (hZ : Measurable Z)

lemma row (a : Bool) :
    (binaryLaw μ W Z hW hZ).mass a false + (binaryLaw μ W Z hW hZ).mass a true =
      μ.real (W ⁻¹' {a}) :=
  real_bool_partition μ Z hZ _ (hW (measurableSet_singleton a))

lemma column (b : Bool) :
    (binaryLaw μ W Z hW hZ).mass false b + (binaryLaw μ W Z hW hZ).mass true b =
      μ.real (Z ⁻¹' {b}) := by
  simpa only [binaryLaw, Set.inter_comm] using
    real_bool_partition μ W hW (Z ⁻¹' {b}) (hZ (measurableSet_singleton b))

lemma input_eq : (binaryLaw μ W Z hW hZ).input = μ.real (W ⁻¹' {true}) := row hW hZ true
lemma output_eq : (binaryLaw μ W Z hW hZ).output = μ.real (Z ⁻¹' {true}) := column hW hZ true

private lemma bool_set_cases (s : Set Bool) :
    s = ∅ ∨ s = {false} ∨ s = {true} ∨ s = Set.univ := by
  classical
  by_cases hf : false ∈ s <;> by_cases ht : true ∈ s
  · right; right; right; ext b; cases b <;> simp_all
  · right; left; ext b; cases b <;> simp_all
  · right; right; left; ext b; cases b <;> simp_all
  · left; ext b; cases b <;> simp_all

/-- The table's product-factorization criterion is mathlib probabilistic independence. -/
theorem independent_iff :
    (binaryLaw μ W Z hW hZ).IsIndependent ↔ ProbabilityTheory.IndepFun W Z μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  constructor
  · intro h s t _ _
    have hsingle (a b : Bool) :
        μ (W ⁻¹' {a} ∩ Z ⁻¹' {b}) = μ (W ⁻¹' {a}) * μ (Z ⁻¹' {b}) := by
      have h' := h a b
      rw [row hW hZ, column hW hZ] at h'
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simpa only [ENNReal.toReal_mul, Measure.real, binaryLaw] using h'
    rcases bool_set_cases s with rfl | rfl | rfl | rfl <;>
      rcases bool_set_cases t with rfl | rfl | rfl | rfl
    all_goals try simp only [Set.preimage_empty, Set.empty_inter, Set.inter_empty, measure_empty,
      zero_mul, mul_zero, Set.preimage_univ, Set.univ_inter, Set.inter_univ, measure_univ,
      one_mul, mul_one]
    all_goals first | exact hsingle false false | exact hsingle false true |
      exact hsingle true false | exact hsingle true true
  · intro h a b
    have h' := congrArg ENNReal.toReal
      (h {a} {b} (measurableSet_singleton a) (measurableSet_singleton b))
    rw [row hW hZ, column hW hZ]
    simpa only [ENNReal.toReal_mul, Measure.real, binaryLaw] using h'

end binaryLaw

/-- Shannon mutual information of two measurable binary random variables, in nats. -/
def binaryMutualInfo (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) : ℝ :=
  (binaryLaw μ W Z hW hZ).mutualInfo

/-- The exact distribution-dependent coefficient from equation (2.2), with the paper's
zero convention at deterministic marginals. The conditional channel is reconstructed from
the actual joint law; no distributional representation is an extra assumption. -/
def binaryContraction (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) : ℝ :=
  (binaryLaw μ W Z hW hZ).contraction

/-- DSBS means equality of opposite joint atom probabilities. -/
def BinaryDSBS (W Z : Ω → Bool) : Prop :=
  μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {false}) = μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {true}) ∧
  μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {true}) = μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {false})

/-- The entropy definition is the sum over the actual four joint events. -/
theorem binaryMutualInfo_eq_entropy (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ =
      H (μ.real (W ⁻¹' {true})) + H (μ.real (Z ⁻¹' {true})) -
        (Real.negMulLog (μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {false})) +
         Real.negMulLog (μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {true})) +
         Real.negMulLog (μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {false})) +
         Real.negMulLog (μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {true}))) := by
  unfold binaryMutualInfo BinaryLaw.mutualInfo
  rw [binaryLaw.input_eq hW hZ, binaryLaw.output_eq hW hZ]
  rfl

/-- The random-variable coefficient agrees with the finite-alphabet KL coefficient,
not merely with a chosen scalar expression. -/
theorem binaryContraction_eq_coefficient (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    let P := binaryLaw μ W Z hW hZ
    binaryContraction μ W Z hW hZ =
      FiniteInfo.coefficient (FiniteInfo.bernoulli P.input P.valid.1)
        (FiniteInfo.binaryChannel P.left P.right P.valid.2.1 P.valid.2.2) := by
  dsimp only
  exact (FiniteInfo.coefficient_binary (binaryLaw μ W Z hW hZ).valid).symm

/-- Theorem 2.1 on an arbitrary probability space. -/
theorem binary_random_variable_bound (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ ≤ phi (binaryContraction μ W Z hW hZ) :=
  BinaryLaw.sharp_bound _

/-- The complete equality statement in ordinary probabilistic terms. -/
theorem binary_random_variable_equality_iff (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ = phi (binaryContraction μ W Z hW hZ) ↔
      ProbabilityTheory.IndepFun W Z μ ∨ BinaryDSBS μ W Z := by
  change (binaryLaw μ W Z hW hZ).mutualInfo = phi (binaryLaw μ W Z hW hZ).contraction ↔ _
  rw [BinaryLaw.sharp_equality_iff, binaryLaw.independent_iff hW hZ]
  rfl

end RandomVariables

/-! ## Finite event probabilities and binary observations

把任意概率空间上的有限取值随机变量变成有限概率表，并验证二元函数输出的概率。
-/

@[expose] public noncomputable section FiniteRandomVariables

open MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Probabilities of finite observations sum over the actual singleton events. -/
theorem measureReal_finite_preimage (X : Ω → α) (hX : Measurable X) (A : Set α) :
    μ.real (X ⁻¹' A) = ∑ a, if a ∈ A then μ.real (X ⁻¹' {a}) else 0 := by
  classical
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ.filter (· ∈ A))
    (fun a _ => hX (measurableSet_singleton a))
  simp only [Finset.sum_filter] at h
  simpa using h.symm

/-- The finite law of a measurable random variable, with no assumptions on its support. -/
def finiteLaw (X : Ω → α) (hX : Measurable X) : FiniteInfo.Law α where
  mass a := μ.real (X ⁻¹' {a})
  nonneg _ := measureReal_nonneg
  total := by
    have h := measureReal_finite_preimage μ X hX Set.univ
    simpa only [Set.preimage_univ, probReal_univ, Set.mem_univ, ↓reduceIte] using h.symm

/-- The probability table of deterministic binary observations is the actual pushforward
of the finite joint probability table. -/
theorem binaryLaw_mass_eq_sum (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) (f : α → Bool) (g : β → Bool) (a b : Bool) :
    (binaryLaw μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY)).mass a b =
      ∑ x, ∑ y, if f x = a ∧ g y = b then μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) else 0 := by
  have h := measureReal_finite_preimage μ (fun ω => (X ω, Y ω)) (hX.prodMk hY)
    {z : α × β | f z.1 = a ∧ g z.2 = b}
  rw [Fintype.sum_prod_type] at h
  have hp (x : α) (y : β) :
      (fun ω => (X ω, Y ω)) ⁻¹' {(x,y)} = X ⁻¹' {x} ∩ Y ⁻¹' {y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff]
  simp only [hp, Set.mem_ofPred_eq] at h
  exact h

end FiniteRandomVariables

end BinaryPairBound
