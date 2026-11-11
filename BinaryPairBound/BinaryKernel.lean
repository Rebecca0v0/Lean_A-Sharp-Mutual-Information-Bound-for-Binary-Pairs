module

public import BinaryPairBound.FiniteContraction
public import BinaryPairBound.ReverseChannel
public import BinaryPairBound.BinaryLaw

noncomputable section
@[expose] public section
open scoped BigOperators

namespace BinaryPairBound.FiniteInfo

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

end BinaryPairBound.FiniteInfo
