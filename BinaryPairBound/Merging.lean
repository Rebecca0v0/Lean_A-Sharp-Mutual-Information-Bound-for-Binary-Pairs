module

public import BinaryPairBound.ScalarEntropy
public import BinaryPairBound.Curvature

noncomputable section

@[expose] public section

namespace BinaryPairBound

def posteriorZero (s c d : ℝ) : ℝ := s * d / (1 - q c d s)
def posteriorOne (s c d : ℝ) : ℝ := s * (1 - d) / q c d s

lemma q_mem_Ioo_of_interior {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    q c d s ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 := mul_pos (sub_pos.mpr hs.2) hc.1
  have h1 := mul_pos hs.1 (sub_pos.mpr hd.2)
  have h2 := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hc.2)
  have h3 := mul_pos hs.1 hd.1
  unfold q k
  constructor <;> nlinarith

lemma posteriorZero_mem_Ioo {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    posteriorZero s c d ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq := q_mem_Ioo_of_interior hs hc hd
  refine ⟨div_pos (mul_pos hs.1 hd.1) (sub_pos.mpr hq.2), ?_⟩
  apply (div_lt_one (sub_pos.mpr hq.2)).2
  have h := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hc.2)
  unfold q k
  nlinarith

lemma posteriorOne_mem_Ioo {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    posteriorOne s c d ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq := q_mem_Ioo_of_interior hs hc hd
  refine ⟨div_pos (mul_pos hs.1 (sub_pos.mpr hd.2)) hq.1, ?_⟩
  apply (div_lt_one hq.1).2
  have h := mul_pos (sub_pos.mpr hs.2) hc.1
  unfold q k
  nlinarith

lemma weighted_binary_entropy {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * H (a / (a + b)) =
      -a * Real.log a - b * Real.log b + (a + b) * Real.log (a + b) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  rw [H_eq, show 1 - a / (a + b) = b / (a + b) by field_simp; ring]
  rw [Real.log_div (ne_of_gt ha) hab, Real.log_div (ne_of_gt hb) hab]
  field_simp
  ring

/-- The finite Bayes entropy identity used at the start of Proposition 7.2. -/
theorem J_eq_posterior_entropy {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    J s c d = H s - ((1 - q c d s) * H (posteriorZero s c d) +
      q c d s * H (posteriorOne s c d)) := by
  have hq := q_mem_Ioo_of_interior hs hc hd
  have ha := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hc.2)
  have hb := mul_pos hs.1 hd.1
  have he := mul_pos (sub_pos.mpr hs.2) hc.1
  have hf := mul_pos hs.1 (sub_pos.mpr hd.2)
  have hcol0 := weighted_binary_entropy hb ha
  have hcol1 := weighted_binary_entropy hf he
  have hrow0 := weighted_binary_entropy he ha
  have hrow1 := weighted_binary_entropy hb hf
  have hin := weighted_binary_entropy hs.1 (sub_pos.mpr hs.2)
  have hout := weighted_binary_entropy hq.1 (sub_pos.mpr hq.2)
  have hsum0 : s * d + (1 - s) * (1 - c) = 1 - q c d s := by unfold q k; ring
  have hsum1 : s * (1 - d) + (1 - s) * c = q c d s := by unfold q k; ring
  have hsumr0 : (1 - s) * c + (1 - s) * (1 - c) = 1 - s := by ring
  have hsumr1 : s * d + s * (1 - d) = s := by ring
  rw [hsum0] at hcol0
  rw [hsum1] at hcol1
  rw [hsumr0, mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hs.2))] at hrow0
  rw [hsumr1, mul_div_cancel_left₀ _ (ne_of_gt hs.1)] at hrow1
  simp only [add_sub_cancel, div_one, one_mul, Real.log_one, mul_zero, add_zero] at hin hout
  unfold J posteriorZero posteriorOne
  linarith

/-- Twice the geometric mean of the two Bernoulli masses. -/
def posteriorAmplitude (p : ℝ) : ℝ := 2 * Real.sqrt (p * (1 - p))

lemma posteriorAmplitude_mem_Icc {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    posteriorAmplitude p ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := Real.sqrt_nonneg (p * (1 - p))
  have he := Real.sq_sqrt (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  unfold posteriorAmplitude
  constructor <;> nlinarith [sq_nonneg (2 * p - 1)]

lemma weighted_posteriorAmplitude {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * posteriorAmplitude (a / (a + b)) = 2 * Real.sqrt (a * b) := by
  have hab : 0 < a + b := add_pos ha hb
  have hp : a / (a + b) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_pos ha hab).le, (div_le_one hab).mpr (by linarith)⟩
  have hp' := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hs : (a + b) * Real.sqrt (a / (a + b) * (1 - a / (a + b))) = Real.sqrt (a * b) := by
    apply (sq_eq_sq₀ (mul_nonneg hab.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hp', Real.sq_sqrt (mul_pos ha hb).le]
    field_simp
    ring
  unfold posteriorAmplitude
  linarith

/-- The Bhattacharyya affinity of the two channel rows. -/
def channelAffinity (c d : ℝ) : ℝ :=
  Real.sqrt ((1 - c) * d) + Real.sqrt (c * (1 - d))

lemma channelAffinity_sq {c d : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) : (channelAffinity c d) ^ 2 = 1 - eta c d := by
  have hA := mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hd.2)
  have hB := mul_nonneg hc.1 hd.1
  have hC := mul_nonneg (sub_nonneg.mpr hc.2) hd.1
  have hE := mul_nonneg hc.1 (sub_nonneg.mpr hd.2)
  have hcross : Real.sqrt ((1 - c) * (1 - d)) * Real.sqrt (c * d) =
      Real.sqrt ((1 - c) * d) * Real.sqrt (c * (1 - d)) := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_mul hC]
    congr 1
    ring
  unfold channelAffinity eta
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hC, Real.sq_sqrt hE]

lemma channelAffinity_eq_sqrt {c d : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) : channelAffinity c d = Real.sqrt (1 - eta c d) := by
  rw [← channelAffinity_sq hc hd, Real.sqrt_sq]
  exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The posterior amplitude mean calculated by Bayes' formula in Section 7. -/
theorem posteriorAmplitude_mean {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - q c d s) * posteriorAmplitude (posteriorZero s c d) +
      q c d s * posteriorAmplitude (posteriorOne s c d) =
      2 * Real.sqrt (s * (1 - s) * (1 - eta c d)) := by
  have ha := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hc.2)
  have hb := mul_pos hs.1 hd.1
  have he := mul_pos (sub_pos.mpr hs.2) hc.1
  have hf := mul_pos hs.1 (sub_pos.mpr hd.2)
  have h0 := weighted_posteriorAmplitude hb ha
  have h1 := weighted_posteriorAmplitude hf he
  have hsum0 : s * d + (1 - s) * (1 - c) = 1 - q c d s := by unfold q k; ring
  have hsum1 : s * (1 - d) + (1 - s) * c = q c d s := by unfold q k; ring
  rw [hsum0] at h0
  rw [hsum1] at h1
  unfold posteriorZero posteriorOne
  rw [h0, h1]
  have hp : 0 ≤ s * (1 - s) := (mul_pos hs.1 (sub_pos.mpr hs.2)).le
  rw [show s * d * ((1 - s) * (1 - c)) = s * (1 - s) * ((1 - c) * d) by ring,
    show s * (1 - d) * ((1 - s) * c) = s * (1 - s) * (c * (1 - d)) by ring]
  rw [Real.sqrt_mul hp, Real.sqrt_mul hp, Real.sqrt_mul hp]
  rw [← channelAffinity_eq_sqrt ⟨hc.1.le, hc.2.le⟩ ⟨hd.1.le, hd.2.le⟩]
  unfold channelAffinity
  ring

/-- The entropy lower bound from two-point Jensen, written as an information upper bound. -/
theorem J_le_posterior_curve {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) :
    J s c d ≤ H s - posteriorEntropyCurve (2 * Real.sqrt (s * (1 - s) * (1 - eta c d))) := by
  have hp0 := posteriorZero_mem_Ioo hs hc hd
  have hp1 := posteriorOne_mem_Ioo hs hc hd
  have hq := q_mem_Ioo_of_interior hs hc hd
  have hj := posteriorEntropyCurve_jensen
    (posteriorAmplitude_mem_Icc ⟨hp0.1.le, hp0.2.le⟩)
    (posteriorAmplitude_mem_Icc ⟨hp1.1.le, hp1.2.le⟩) ⟨hq.1.le, hq.2.le⟩
  rw [posteriorAmplitude_mean hs hc hd] at hj
  have he0 : posteriorEntropyCurve (posteriorAmplitude (posteriorZero s c d)) = H (posteriorZero s c d) :=
    posteriorEntropyCurve_two_sqrt ⟨hp0.1.le, hp0.2.le⟩
  have he1 : posteriorEntropyCurve (posteriorAmplitude (posteriorOne s c d)) = H (posteriorOne s c d) :=
    posteriorEntropyCurve_two_sqrt ⟨hp1.1.le, hp1.2.le⟩
  rw [he0, he1] at hj
  rw [J_eq_posterior_entropy hs hc hd]
  linarith

lemma phi_bias {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1) :
    phi ((1 - 2 * s) ^ 2) = Real.log 2 - H s := by
  unfold phi
  rw [Real.sqrt_sq_eq_abs]
  by_cases hh : s ≤ 1 / 2
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * s)]
    rw [show (1 - (1 - 2 * s)) / 2 = s by ring]
  · rw [abs_of_nonpos (by linarith : 1 - 2 * s ≤ 0)]
    rw [show (1 - -(1 - 2 * s)) / 2 = 1 - s by ring]
    simp only [H, Real.binEntropy_one_sub]

lemma posterior_curve_phi_identity {s e : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (he : e ≤ 1) :
    H s - posteriorEntropyCurve (2 * Real.sqrt (s * (1 - s) * (1 - e))) =
      phi (e + (1 - e) * (1 - 2 * s) ^ 2) - phi ((1 - 2 * s) ^ 2) := by
  rw [phi_bias hs]
  have hp := mul_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr hs.2)) (sub_nonneg.mpr he)
  have hsq : (2 * Real.sqrt (s * (1 - s) * (1 - e))) ^ 2 = 4 * s * (1 - s) * (1 - e) := by
    nlinarith [Real.sq_sqrt hp]
  unfold posteriorEntropyCurve phi
  rw [hsq, show 1 - 4 * s * (1 - s) * (1 - e) = e + (1 - e) * (1 - 2 * s) ^ 2 by ring]
  ring

/-- The posterior-entropy argument bounds information by the channel-wide expression.
This is NOT yet the distribution-dependent bound of Theorem 2.1. -/
theorem J_le_phi_eta {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d < 1) :
    J s c d ≤ phi (eta c d) := by
  have he : eta c d ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨eta_pos ⟨hc.1.le, hc.2.le⟩ ⟨hd.1.le, hd.2.le⟩ (ne_of_lt hcd), eta_lt_one hc hd⟩
  have hr : (1 - 2 * s) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg _
    · nlinarith [mul_pos hs.1 (sub_pos.mpr hs.2)]
  calc
    J s c d ≤ H s - posteriorEntropyCurve (2 * Real.sqrt (s * (1 - s) * (1 - eta c d))) :=
      J_le_posterior_curve hs hc hd
    _ = phi (eta c d + (1 - eta c d) * (1 - 2 * s) ^ 2) - phi ((1 - 2 * s) ^ 2) :=
      posterior_curve_phi_identity ⟨hs.1.le, hs.2.le⟩ he.2.le
    _ ≤ phi (eta c d) := phi_increment_le he hr

/-- Equality in the channel-wide bound requires a uniform input. -/
theorem input_half_of_J_eq_phi_eta {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d < 1)
    (hJ : J s c d = phi (eta c d)) : s = 1 / 2 := by
  have he : eta c d ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨eta_pos ⟨hc.1.le, hc.2.le⟩ ⟨hd.1.le, hd.2.le⟩ (ne_of_lt hcd), eta_lt_one hc hd⟩
  have hr : (1 - 2 * s) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sq_nonneg _
    · nlinarith [mul_pos hs.1 (sub_pos.mpr hs.2)]
  have hh := J_le_posterior_curve hs hc hd
  rw [posterior_curve_phi_identity ⟨hs.1.le, hs.2.le⟩ he.2.le, hJ] at hh
  have heq := le_antisymm (phi_increment_le he hr) hh
  have hz := (phi_increment_eq_iff he hr).mp heq
  nlinarith [sq_nonneg (1 - 2 * s)]

lemma eta_symmetric {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) : eta c c = (1 - 2 * c) ^ 2 := by
  unfold eta
  rw [Real.sqrt_mul_self (sub_nonneg.mpr hc.2), Real.sqrt_mul_self hc.1]
  ring

/-- Uniform symmetric channels attain the channel-wide bound. -/
theorem J_half_symmetric_eq_phi_eta {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    J (1 / 2) c c = phi (eta c c) := by
  rw [eta_symmetric hc, phi_bias hc]
  unfold J
  rw [show q c c (1 / 2) = 1 / 2 by unfold q k; ring]
  have hH : H (1 / 2) = Real.log 2 := by simpa only [one_div] using Real.binEntropy_two_inv
  rw [hH]
  ring

/-- The equality classification in Proposition 7.2 at the distinguished input.
Identifying this configuration with maximizers under a fixed `S` cap is separate. -/
theorem merging_eq_iff_dsbs {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d < 1)
    (hs0 : s = distinguishedInput c d) :
    J s c d = phi (eta c d) ↔ DSBS s c d := by
  constructor
  · intro hJ
    have hh := input_half_of_J_eq_phi_eta hs hc hd hcd hJ
    have hcdeq := (distinguishedInput_eq_half_iff hc hd hcd).mp (hs0.symm.trans hh)
    exact ⟨hh, hcdeq⟩
  · rintro ⟨rfl, hceq⟩
    subst d
    exact J_half_symmetric_eq_phi_eta ⟨hc.1.le, hc.2.le⟩

end BinaryPairBound
