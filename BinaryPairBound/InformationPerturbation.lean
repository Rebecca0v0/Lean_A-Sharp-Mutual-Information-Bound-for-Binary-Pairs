module

public import BinaryPairBound.Perturbation
public import BinaryPairBound.ScalarEntropy

/-!
# Information in input/output/slope coordinates

The derivatives below are actual derivatives of the mutual information,
including the chain rule for an arbitrary differentiable family. Constructing
the feasible implicit contact family is a separate obligation.
-/

noncomputable section

@[expose] public section

namespace BinaryPairBound

/-- Mutual information in the coordinates of Section 5. -/
def informationCoords (s qv kv : ℝ) : ℝ :=
  H qv - (1 - s) * H (qv - kv * s) - s * H (qv + kv * (1 - s))

theorem informationCoords_eq_J (s qv kv : ℝ) :
    informationCoords s qv kv = J s (qv - kv * s) (1 - qv - kv * (1 - s)) := by
  have hq : q (qv - kv * s) (1 - qv - kv * (1 - s)) s = qv := by
    unfold q k
    ring
  have hb : qv + kv * (1 - s) = 1 - (1 - qv - kv * (1 - s)) := by ring
  unfold informationCoords J
  rw [hq, hb]
  simp only [H, Real.binEntropy_one_sub]

theorem informationCoords_channel (s c d : ℝ) :
    informationCoords s (q c d s) (k c d) = J s c d := by
  rw [informationCoords_eq_J]
  congr 1 <;> unfold q k <;> ring

theorem hasDerivAt_H {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt H (-logOdds x) x := by
  convert! Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (ne_of_lt hx.2) using 1
  unfold logOdds
  ring

/-- Chain rule, with all three coordinates allowed to vary. -/
theorem hasDerivAt_informationCoords_comp
    {sf qf kf : ℝ → ℝ} {sv qv kv t : ℝ}
    (hs : HasDerivAt sf sv t) (hq : HasDerivAt qf qv t) (hk : HasDerivAt kf kv t)
    (hqI : qf t ∈ Set.Ioo (0 : ℝ) 1)
    (hcI : qf t - kf t * sf t ∈ Set.Ioo (0 : ℝ) 1)
    (hbI : qf t + kf t * (1 - sf t) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => informationCoords (sf z) (qf z) (kf z))
      (sv * (H (qf t - kf t * sf t) - H (qf t + kf t * (1 - sf t)) -
          kf t * ((1 - sf t) * logOdds (qf t - kf t * sf t) +
            sf t * logOdds (qf t + kf t * (1 - sf t)))) +
       qv * ((1 - sf t) * logOdds (qf t - kf t * sf t) +
          sf t * logOdds (qf t + kf t * (1 - sf t)) - logOdds (qf t)) +
       kv * (sf t * (1 - sf t) *
          (logOdds (qf t + kf t * (1 - sf t)) - logOdds (qf t - kf t * sf t)))) t := by
  have hQ := (hasDerivAt_H hqI).comp t hq
  have hC := (hasDerivAt_H hcI).comp t (hq.sub (hk.mul hs))
  have hB := (hasDerivAt_H hbI).comp t (hq.add (hk.mul (hs.const_sub 1)))
  convert! (hQ.sub ((hs.const_sub 1).mul hC)).sub (hs.mul hB) using 1
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  ring

theorem hasDerivAt_informationCoords_k {s qv kv : ℝ}
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => informationCoords s qv z)
      (s * (1 - s) * (logOdds (qv + kv * (1 - s)) - logOdds (qv - kv * s))) kv := by
  simpa only [zero_mul, zero_add, one_mul, id_eq] using
    hasDerivAt_informationCoords_comp (hasDerivAt_const kv s) (hasDerivAt_const kv qv)
      (hasDerivAt_id kv) hq hc hb

/-- Increasing the channel slope at fixed marginals strictly increases information. -/
theorem informationCoords_deriv_k_pos {s qv kv : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hk : 0 < kv)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) :
    0 < deriv (fun z => informationCoords s qv z) kv := by
  rw [(hasDerivAt_informationCoords_k hq hc hb).deriv]
  apply mul_pos (mul_pos hs.1 (sub_pos.mpr hs.2))
  exact sub_pos.mpr (logOdds_strictMonoOn hc hb (by linarith))

theorem hasDerivAt_informationCoords_s {s qv kv : ℝ}
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => informationCoords z qv kv)
      (D (qv + kv * (1 - s)) (qv - kv * s) -
        s * kv * (logOdds (qv + kv * (1 - s)) - logOdds (qv - kv * s))) s := by
  have h := hasDerivAt_informationCoords_comp (hasDerivAt_id s)
    (hasDerivAt_const s qv) (hasDerivAt_const s kv) hq hc hb
  convert! h using 1
  simp only [id_eq, one_mul, zero_mul, add_zero]
  rw [D, H_eq (qv - kv * s)]
  unfold logOdds
  ring

theorem hasDerivAt_informationCoords_q {s qv kv : ℝ}
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => informationCoords s z kv)
      ((1 - s) * logOdds (qv - kv * s) +
        s * logOdds (qv + kv * (1 - s)) - logOdds qv) qv := by
  simpa only [zero_mul, zero_add, one_mul, id_eq, add_zero] using
    hasDerivAt_informationCoords_comp (hasDerivAt_const qv s) (hasDerivAt_id qv)
      (hasDerivAt_const qv kv) hq hc hb

/-- A logarithmic upper bound, proved by differentiating its positive excess. -/
lemma entropyLogRatio_lt_rational {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    entropyLogRatio x < 2 * x / (1 - x ^ 2) := by
  let f : ℝ → ℝ := fun t => 2 * t / (1 - t ^ 2) - entropyLogRatio t
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt f (4 * t ^ 2 / (1 - t ^ 2) ^ 2) t := by
    intro t ht
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
    have hn : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2, hx.2]
    have h := (((hasDerivAt_id t).const_mul 2).div
      (((hasDerivAt_id t).pow 2).const_sub 1) hn).sub (hasDerivAt_entropyLogRatio htI)
    convert! h using 1
    simp only [id_eq, Pi.pow_apply]
    field_simp
    ring
  have hm : StrictMonoOn f (Set.Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · intro t ht
      exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo 0 x := by simpa only [interior_Icc] using ht
      rw [(hf t ⟨htI.1.le, htI.2.le⟩).deriv]
      exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos htI.1))
        (sq_pos_of_ne_zero (by nlinarith [htI.1, htI.2, hx.2]))
  have hh := hm ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  dsimp [f] at hh
  simp only [entropyLogRatio, add_zero, sub_zero, Real.log_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, zero_div] at hh
  dsimp [entropyLogRatio]
  linarith

lemma entropyLogRatio_div_strictMonoOn :
    StrictMonoOn (fun x : ℝ => entropyLogRatio x / x) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro x hx
    exact ((hasDerivAt_entropyLogRatio ⟨by linarith [hx.1], hx.2⟩).div
      (hasDerivAt_id x) (ne_of_gt hx.1)).continuousAt.continuousWithinAt
  · intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hx
    have h := (hasDerivAt_entropyLogRatio ⟨by linarith [hxI.1], hxI.2⟩).div
      (hasDerivAt_id x) (ne_of_gt hxI.1)
    change 0 < deriv (entropyLogRatio / id) x
    rw [h.deriv]
    simp only [id_eq]
    apply div_pos _ (sq_pos_of_pos hxI.1)
    have hlt := entropyLogRatio_lt_rational hxI
    convert! sub_pos.mpr hlt using 1
    ring

/-- The normalized log ratio agrees with the unnormalized endpoint ratio. -/
lemma entropyLogRatio_normalized {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    entropyLogRatio ((b - a) / (a + b)) = Real.log b - Real.log a := by
  have hab : a + b ≠ 0 := by positivity
  have hp : 1 + (b - a) / (a + b) = (2 * b) / (a + b) := by field_simp; ring
  have hm : 1 - (b - a) / (a + b) = (2 * a) / (a + b) := by field_simp; ring
  rw [entropyLogRatio, hp, hm,
    Real.log_div (by positivity) hab, Real.log_div (by positivity) hab,
    Real.log_mul (by norm_num) (ne_of_gt hb), Real.log_mul (by norm_num) (ne_of_gt ha)]
  ring

/-- Bernoulli divergence is larger in the increasing direction when the
endpoints lie symmetrically no farther right than one half. -/
theorem D_reverse_le_of_sum_le_one {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hab : a < b) (hsum : a + b ≤ 1) : D a b ≤ D b a := by
  let u := (b - a) / (a + b)
  let v := (b - a) / (2 - a - b)
  have hsum0 : 0 < a + b := add_pos ha.1 hb.1
  have hsum2 : 0 < 2 - a - b := by linarith
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [u]
    exact ⟨div_pos (sub_pos.mpr hab) hsum0, (div_lt_one hsum0).mpr (by linarith [ha.1])⟩
  have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [v]
    exact ⟨div_pos (sub_pos.mpr hab) hsum2, (div_lt_one hsum2).mpr (by linarith [hb.2])⟩
  have hvu : v ≤ u := by
    dsimp [u, v]
    apply div_le_div_of_nonneg_left (sub_nonneg.mpr hab.le) hsum0
    linarith
  have hmono := entropyLogRatio_div_strictMonoOn.monotoneOn hv hu hvu
  have hLu : entropyLogRatio u = Real.log b - Real.log a :=
    entropyLogRatio_normalized ha.1 hb.1
  have hLv : entropyLogRatio v = Real.log (1 - a) - Real.log (1 - b) := by
    have heq : v = ((1 - a) - (1 - b)) / ((1 - b) + (1 - a)) := by dsimp [v]; congr 1 <;> ring
    rw [heq]
    exact entropyLogRatio_normalized (sub_pos.mpr hb.2) (sub_pos.mpr ha.2)
  rw [hLu, hLv] at hmono
  have hid : D b a - D a b = (b - a) *
      ((Real.log b - Real.log a) / u - (Real.log (1 - a) - Real.log (1 - b)) / v) := by
    rw [D, D, H_eq, H_eq]
    dsimp [u, v]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hsum0, ne_of_gt hsum2]
    ring
  have hnonneg := mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hmono)
  rw [← hid] at hnonneg
  linarith

/-- The sum of the two KL orientations is slope times log-odds gap. -/
lemma D_add_reverse (a b : ℝ) :
    D a b + D b a = (b - a) * (logOdds b - logOdds a) := by
  rw [D, D, H_eq, H_eq]
  unfold logOdds
  ring

/-- The strict scalar inequality behind `E(L) < 1/2`, without exponentials. -/
lemma input_contact_excess_pos {s r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hsr : s < r) :
    0 < 1 / 2 - s + s * (1 - s) / (r - s) - 1 / (logOdds r - logOdds s) := by
  let a := s * (1 - r)
  let b := r * (1 - s)
  have ha : 0 < a := mul_pos hs.1 (sub_pos.mpr hr.2)
  have hb : 0 < b := mul_pos hr.1 (sub_pos.mpr hs.2)
  have hab : a < b := by dsimp [a, b]; nlinarith
  have hsum : 0 < a + b := add_pos ha hb
  have ht : (b - a) / (a + b) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hab) hsum, (div_lt_one hsum).mpr (by linarith)⟩
  have hlog : Real.log b - Real.log a = logOdds r - logOdds s := by
    dsimp [a, b, logOdds]
    rw [Real.log_mul (ne_of_gt hr.1) (ne_of_gt (sub_pos.mpr hs.2)),
      Real.log_mul (ne_of_gt hs.1) (ne_of_gt (sub_pos.mpr hr.2))]
    ring
  have hgt := entropyLogRatio_gt_two_mul ht
  rw [entropyLogRatio_normalized ha hb, hlog] at hgt
  have hinv := one_div_lt_one_div_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) ht.1) hgt
  have hid : 1 / (2 * ((b - a) / (a + b))) = 1 / 2 - s + s * (1 - s) / (r - s) := by
    dsimp [a, b]
    have hba : r * (1 - s) - s * (1 - r) ≠ 0 := by nlinarith
    field_simp [hba, ne_of_gt (sub_pos.mpr hsr)]
    ring
  rw [hid] at hinv
  linarith

/-- The positive `s` direction in Lemma C.1, with the explicit contact slope
from (C.2). This is the scalar sign theorem; it does not assert that a feasible
implicit family exists. -/
theorem informationCoords_contact_s_direction_pos {s r qv kv : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hsr : s < r) (hk : 0 < kv)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : (qv - kv * s) + (qv + kv * (1 - s)) ≤ 1) :
    0 < deriv (fun z => informationCoords z qv kv) s +
      deriv (fun z => informationCoords s qv z) kv *
        (kv / (r - s) - kv / ((logOdds r - logOdds s) * s * (1 - s))) := by
  let a := qv - kv * s
  let b := qv + kv * (1 - s)
  let M := logOdds b - logOdds a
  have hba : a < b := by dsimp [a, b]; linarith
  have hM : 0 < M := sub_pos.mpr (logOdds_strictMonoOn hc hb hba)
  have hhalf : kv * M / 2 ≤ D b a := by
    have hsum := D_add_reverse a b
    have hrev := D_reverse_le_of_sum_le_one hc hb hba hcd
    have hid : b - a = kv := by dsimp [a, b]; ring
    rw [hid] at hsum
    dsimp [M]
    linarith
  have hgap := input_contact_excess_pos hs hr hsr
  have hL : 0 < logOdds r - logOdds s := sub_pos.mpr (logOdds_strictMonoOn hs hr hsr)
  rw [(hasDerivAt_informationCoords_s hq hc hb).deriv,
    (hasDerivAt_informationCoords_k hq hc hb).deriv]
  change 0 < D b a - s * kv * M + s * (1 - s) * M *
    (kv / (r - s) - kv / ((logOdds r - logOdds s) * s * (1 - s)))
  have hid : D b a - s * kv * M + s * (1 - s) * M *
      (kv / (r - s) - kv / ((logOdds r - logOdds s) * s * (1 - s))) =
      D b a - kv * M / 2 + kv * M *
        (1 / 2 - s + s * (1 - s) / (r - s) - 1 / (logOdds r - logOdds s)) := by
    field_simp [ne_of_gt hs.1, ne_of_gt (sub_pos.mpr hs.2), ne_of_gt hL,
      ne_of_gt (sub_pos.mpr hsr)]
    ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hhalf) (mul_pos (mul_pos hk hM) hgap)

/-- The actual one-variable chain rule in (C.1) for an input perturbation. -/
theorem hasDerivAt_informationCoords_input_family {kf : ℝ → ℝ} {s qv v : ℝ}
    (hk : HasDerivAt kf v s)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kf s * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kf s * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => informationCoords z qv (kf z))
      (deriv (fun z => informationCoords z qv (kf s)) s +
        deriv (fun z => informationCoords s qv z) (kf s) * v) s := by
  rw [(hasDerivAt_informationCoords_s hq hc hb).deriv,
    (hasDerivAt_informationCoords_k hq hc hb).deriv]
  have h := hasDerivAt_informationCoords_comp (hasDerivAt_id s)
    (hasDerivAt_const s qv) hk hq hc hb
  convert! h using 1
  simp only [id_eq, one_mul, zero_mul, add_zero]
  rw [D, H_eq (qv - kf s * s)]
  unfold logOdds
  ring

/-- The actual one-variable chain rule in (C.1) for an output perturbation. -/
theorem hasDerivAt_informationCoords_output_family {kf : ℝ → ℝ} {s qv v : ℝ}
    (hk : HasDerivAt kf v qv)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kf qv * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kf qv * (1 - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => informationCoords s z (kf z))
      (deriv (fun z => informationCoords s z (kf qv)) qv +
        deriv (fun z => informationCoords s qv z) (kf qv) * v) qv := by
  rw [(hasDerivAt_informationCoords_q hq hc hb).deriv,
    (hasDerivAt_informationCoords_k hq hc hb).deriv]
  have h := hasDerivAt_informationCoords_comp (hasDerivAt_const qv s)
    (hasDerivAt_id qv) hk hq hc hb
  convert! h using 1
  simp only [id_eq, one_mul, zero_mul, zero_add]
  ring

/-- Lemma C.1 for an actual differentiable family, assuming its differentiated
contact identity. No assumption of a positive information derivative is used.
Existence and cap feasibility of such a family are supplied by `ContactFamily.lean`. -/
theorem informationCoords_contact_input_family_deriv_pos
    {kf : ℝ → ℝ} {lam s qv r v : ℝ}
    (hfamily : HasDerivAt kf v s)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hsr : s < r) (hk : 0 < kf s)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kf s * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kf s * (1 - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf s * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : (qv - kf s * s) + (qv + kf s * (1 - s)) ≤ 1)
    (hGr : deriv (fun z => contactGap lam s qv (kf s) z) r = 0)
    (hchain : deriv (fun z => contactGap lam z qv (kf s) r) s +
      deriv (fun z => contactGap lam s qv z r) (kf s) * v = 0) :
    0 < deriv (fun z => informationCoords z qv (kf z)) s := by
  rw [(hasDerivAt_informationCoords_input_family hfamily hq hc hb).deriv,
    contactGap_implicit_slope_s lam s qv (kf s) r v hs hr hq hqr hk hsr hGr hchain]
  exact informationCoords_contact_s_direction_pos hs hr hsr hk hq hc hb hcd

/-- Differentiate the contact equation along an input family with a moving
second contact. Stationarity later cancels the derivative of that contact. -/
theorem hasDerivAt_contactGap_input_family
    {kf rf : ℝ → ℝ} {lam s qv v w : ℝ}
    (hk : HasDerivAt kf v s) (hrf : HasDerivAt rf w s)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : rf s ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf s * (rf s - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam z qv (kf z) (rf z))
      (deriv (fun z => contactGap lam z qv (kf s) (rf s)) s +
       deriv (fun z => contactGap lam s qv z (rf s)) (kf s) * v +
       deriv (fun z => contactGap lam s qv (kf s) z) (rf s) * w) s := by
  have hY := ((hk.mul (hrf.sub (hasDerivAt_id s))).const_add qv)
  have h1 := hasDerivAt_D_comp hY (hasDerivAt_const s qv) hqr hq
  have h2 := (hasDerivAt_D_comp hrf (hasDerivAt_id s) hr hs).const_mul lam
  rw [(hasDerivAt_contactGap_s lam s qv (kf s) (rf s) hs hr hq hqr).deriv,
    (hasDerivAt_contactGap_k lam s qv (kf s) (rf s) hq hqr).deriv,
    (hasDerivAt_contactGap_r lam s qv (kf s) (rf s) hs hr hq hqr).deriv]
  convert! h1.sub h2 using 1
  simp only [zero_mul, zero_div, add_zero, one_mul, id_eq, Pi.mul_apply, Pi.sub_apply]
  ring

/-- Lemma C.1 for differentiable contact curves satisfying `G = 0` locally
and `G_r = 0` at the reference point. The differentiated constraint is derived
here, rather than required as an additional hypothesis. -/
theorem informationCoords_contact_curve_deriv_pos
    {kf rf : ℝ → ℝ} {lam s qv v w : ℝ}
    (hkf : HasDerivAt kf v s) (hrf : HasDerivAt rf w s)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : rf s ∈ Set.Ioo (0 : ℝ) 1)
    (hsr : s < rf s) (hk : 0 < kf s)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hc : qv - kf s * s ∈ Set.Ioo (0 : ℝ) 1)
    (hb : qv + kf s * (1 - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kf s * (rf s - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : (qv - kf s * s) + (qv + kf s * (1 - s)) ≤ 1)
    (hGr : deriv (fun z => contactGap lam s qv (kf s) z) (rf s) = 0)
    (hG : ∀ᶠ z in nhds s, contactGap lam z qv (kf z) (rf z) = 0) :
    0 < deriv (fun z => informationCoords z qv (kf z)) s := by
  have hder := hasDerivAt_contactGap_input_family (lam := lam) hkf hrf hs hr hq hqr
  have hzero : HasDerivAt (fun z => contactGap lam z qv (kf z) (rf z)) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hG
  have hchain := hder.unique hzero
  rw [hGr, zero_mul, add_zero] at hchain
  exact informationCoords_contact_input_family_deriv_pos hkf hs hr hsr hk hq hc hb hqr hcd hGr hchain

end BinaryPairBound
