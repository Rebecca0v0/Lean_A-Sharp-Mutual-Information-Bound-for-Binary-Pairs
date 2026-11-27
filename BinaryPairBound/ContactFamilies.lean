module

public import BinaryPairBound.BinaryInformation
public import BinaryPairBound.InformationBounds
public import BinaryPairBound.ChannelGeometry
public import BinaryPairBound.CoefficientContinuity
public import BinaryPairBound.SupportingContacts
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Construction of smooth feasible contact families

计算接触方程与互信息的导数，验证隐函数定理条件，构造真正保持约束的光滑变化。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Contact equations and their derivatives

把接触条件写成一个方程，并计算这个方程对各个参数的导数。
-/

@[expose] public noncomputable section Perturbation

/-- The contact equation in input/output/slope coordinates. -/
def contactGap (lam s qv kv r : ℝ) : ℝ :=
  D (qv + kv * (r - s)) qv - lam * D r s

theorem hasDerivAt_contactGap_r (lam s qv kv r : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam s qv kv z)
      (kv * (logOdds (qv + kv * (r - s)) - logOdds qv) -
        lam * (logOdds r - logOdds s)) r := by
  have ha : HasDerivAt (fun z => qv + kv * (z - s)) kv r := by
    convert! (((hasDerivAt_id r).sub_const s).const_mul kv).const_add qv using 1
    simp
  have h1 := (hasDerivAt_D_left hqr hq).comp r ha
  have h2 := (hasDerivAt_D_left hr hs).const_mul lam
  convert! h1.sub h2 using 1
  ring

theorem hasDerivAt_contactGap_k (lam s qv kv r : ℝ)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam s qv z r)
      ((r - s) * (logOdds (qv + kv * (r - s)) - logOdds qv)) kv := by
  have ha : HasDerivAt (fun z => qv + z * (r - s)) (r - s) kv := by
    convert! ((hasDerivAt_id kv).mul_const (r - s)).const_add qv using 1
    simp
  have h1 := (hasDerivAt_D_left hqr hq).comp kv ha
  convert! h1.sub_const (lam * D r s) using 1
  ring

theorem hasDerivAt_contactGap_s (lam s qv kv r : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam z qv kv r)
      (-kv * (logOdds (qv + kv * (r - s)) - logOdds qv) +
        lam * (r - s) / (s * (1 - s))) s := by
  have ha : HasDerivAt (fun z => qv + kv * (r - z)) (-kv) s := by
    convert! (((hasDerivAt_id s).const_sub r).const_mul kv).const_add qv using 1
    simp
  have h1 := (hasDerivAt_D_left hqr hq).comp s ha
  have h2 := (hasDerivAt_D_right hr hs).const_mul lam
  convert! h1.sub h2 using 1
  ring

theorem hasDerivAt_contactGap_q (lam s qv kv r : ℝ)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => contactGap lam s z kv r)
      (logOdds (qv + kv * (r - s)) - logOdds qv -
        kv * (r - s) / (qv * (1 - qv))) qv := by
  have ha : HasDerivAt (fun z => z + kv * (r - s)) 1 qv :=
    (hasDerivAt_id qv).add_const (kv * (r - s))
  have h1 := hasDerivAt_D_comp ha (hasDerivAt_id qv) hqr hq
  convert! h1.sub_const (lam * D r s) using 1
  simp only [id_eq]
  ring

theorem contactGap_deriv_k_pos (lam s qv kv r : ℝ)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hk : 0 < kv) (hsr : s < r) :
    0 < deriv (fun z => contactGap lam s qv z r) kv := by
  rw [(hasDerivAt_contactGap_k lam s qv kv r hq hqr).deriv]
  apply mul_pos (sub_pos.mpr hsr)
  apply sub_pos.mpr
  apply logOdds_strictMonoOn hq hqr
  linarith [mul_pos hk (sub_pos.mpr hsr)]

/-- The stationarity equation in `r` determines the contact cap. -/
theorem contactGap_lambda_eq (lam s qv kv r : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hsr : s < r) (hGr : deriv (fun z => contactGap lam s qv kv z) r = 0) :
    lam = kv * (logOdds (qv + kv * (r - s)) - logOdds qv) /
      (logOdds r - logOdds s) := by
  have hL : 0 < logOdds r - logOdds s := sub_pos.mpr (logOdds_strictMonoOn hs hr hsr)
  rw [(hasDerivAt_contactGap_r lam s qv kv r hs hr hq hqr).deriv] at hGr
  apply (eq_div_iff (ne_of_gt hL)).mpr
  linarith

/-- The `s` slope in (C.2), conditional on the differentiated contact equation.
This does not construct an implicit family. -/
theorem contactGap_implicit_slope_s (lam s qv kv r v : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hk : 0 < kv) (hsr : s < r)
    (hGr : deriv (fun z => contactGap lam s qv kv z) r = 0)
    (hchain : deriv (fun z => contactGap lam z qv kv r) s +
      deriv (fun z => contactGap lam s qv z r) kv * v = 0) :
    v = kv / (r - s) - kv / ((logOdds r - logOdds s) * s * (1 - s)) := by
  have hdel : 0 < logOdds (qv + kv * (r - s)) - logOdds qv := by
    apply sub_pos.mpr
    apply logOdds_strictMonoOn hq hqr
    linarith [mul_pos hk (sub_pos.mpr hsr)]
  have hL : 0 < logOdds r - logOdds s := sub_pos.mpr (logOdds_strictMonoOn hs hr hsr)
  rw [(hasDerivAt_contactGap_s lam s qv kv r hs hr hq hqr).deriv,
    (hasDerivAt_contactGap_k lam s qv kv r hq hqr).deriv] at hchain
  have hv : v =
      (kv * (logOdds (qv + kv * (r - s)) - logOdds qv) -
        lam * (r - s) / (s * (1 - s))) /
      ((r - s) * (logOdds (qv + kv * (r - s)) - logOdds qv)) := by
    apply (eq_div_iff (ne_of_gt (mul_pos (sub_pos.mpr hsr) hdel))).mpr
    nlinarith
  rw [hv, contactGap_lambda_eq lam s qv kv r hs hr hq hqr hsr hGr]
  field_simp [ne_of_gt hdel, ne_of_gt hL, ne_of_gt hs.1,
    ne_of_gt (sub_pos.mpr hs.2), ne_of_gt (sub_pos.mpr hsr)]

/-- The `q` slope in (C.2), conditional on the differentiated contact equation. -/
theorem contactGap_implicit_slope_q (lam s qv kv r v : ℝ)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1)
    (hk : 0 < kv) (hsr : s < r)
    (hchain : deriv (fun z => contactGap lam s z kv r) qv +
      deriv (fun z => contactGap lam s qv z r) kv * v = 0) :
    v = -1 / (r - s) +
      kv / (qv * (1 - qv) * (logOdds (qv + kv * (r - s)) - logOdds qv)) := by
  have hdel : 0 < logOdds (qv + kv * (r - s)) - logOdds qv := by
    apply sub_pos.mpr
    apply logOdds_strictMonoOn hq hqr
    linarith [mul_pos hk (sub_pos.mpr hsr)]
  rw [(hasDerivAt_contactGap_q lam s qv kv r hq hqr).deriv,
    (hasDerivAt_contactGap_k lam s qv kv r hq hqr).deriv] at hchain
  have hv : v =
      (-(logOdds (qv + kv * (r - s)) - logOdds qv) +
        kv * (r - s) / (qv * (1 - qv))) /
      ((r - s) * (logOdds (qv + kv * (r - s)) - logOdds qv)) := by
    apply (eq_div_iff (ne_of_gt (mul_pos (sub_pos.mpr hsr) hdel))).mpr
    nlinarith
  rw [hv]
  field_simp [ne_of_gt hdel, ne_of_gt hq.1, ne_of_gt (sub_pos.mpr hq.2),
    ne_of_gt (sub_pos.mpr hsr)]

end Perturbation

/-! ## Information in input, output, and slope coordinates

改用输入概率、输出概率和信道斜率描述互信息，计算这些量变化时互信息的导数。
-/

@[expose] public noncomputable section InformationPerturbation

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
Existence and cap feasibility of such a family are supplied by `ContactFamilies.lean`. -/
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

end InformationPerturbation

/-! ## Invertibility of the contact equations

证明接触方程的关键行列式不为零，为应用隐函数定理准备条件。
-/

@[expose] public noncomputable section ContactJacobian

theorem contactGap_eq_tangent_sub {lam s c d : ℝ} (hn : Nondegenerate s c d) (x : ℝ) :
    contactGap lam s (q c d s) (k c d) x =
      tangent lam s c d x - entropyCurve lam c d x := by
  have hx : q c d s + k c d * (x - s) = q c d x := by unfold q; ring
  rw [contactGap, hx]
  linarith [equation_4_1 lam s c d x hn.1 hn.2]

theorem hasDerivAt_deriv_contactGap_r {lam s c d r : ℝ}
    (hn : Nondegenerate s c d) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : q c d r ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (fun x => contactGap lam s (q c d s) (k c d) x))
      ((rhoSquared c d r - lam) / (r * (1 - r))) r := by
  have hfun : (fun x => contactGap lam s (q c d s) (k c d) x) =
      (fun x => tangent lam s c d x - entropyCurve lam c d x) :=
    funext (contactGap_eq_tangent_sub hn)
  have heq : deriv (fun x => contactGap lam s (q c d s) (k c d) x) =ᶠ[nhds r]
      (fun x => deriv (entropyCurve lam c d) s - deriv (entropyCurve lam c d) x) := by
    have hi : ∀ᶠ x in nhds r, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hr.1 hr.2
    have ho : ∀ᶠ x in nhds r, q c d x ∈ Set.Ioo (0 : ℝ) 1 :=
      (hasDerivAt_q c d r).continuousAt (Ioo_mem_nhds hqr.1 hqr.2)
    filter_upwards [hi, ho] with x hx hqx
    rw [hfun]
    exact ((hasDerivAt_tangent lam s c d x).sub
      (hasDerivAt_entropyCurve lam x c d hx hqx).differentiableAt.hasDerivAt).deriv
  have hh := ((hasDerivAt_deriv_entropyCurve (lam := lam) hr hqr).const_sub
    (deriv (entropyCurve lam c d) s)).congr_of_eventuallyEq heq
  convert! hh using 1
  ring

theorem contactGap_deriv_r_eq_zero_of_contact {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    deriv (fun x => contactGap lam s (q c d s) (k c d) x) r = 0 := by
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩⟩
  have hfun : (fun x => contactGap lam s (q c d s) (k c d) x) =
      (fun x => tangent lam s c d x - entropyCurve lam c d x) :=
    funext (contactGap_eq_tangent_sub hn)
  rw [hfun]
  change deriv (tangent lam s c d - entropyCurve lam c d) r = 0
  rw [((hasDerivAt_tangent lam s c d r).sub
    (hasDerivAt_entropyCurve lam r c d hr
      (q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩)).differentiableAt.hasDerivAt).deriv]
  rw [supporting_contact_deriv_eq hs hr hc hd hcap hcontact, sub_self]

theorem contactGap_deriv2_r_neg_of_contact {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d ≠ 1) (hlam : lam < eta c d) (hrs : r ≠ s)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    deriv (deriv (fun x => contactGap lam s (q c d s) (k c d) x)) r < 0 := by
  have hS := (supporting_contact_coefficients hs hr hc hd hrs hcap hcontact).2
  have hrne : r ≠ distinguishedInput c d := by
    intro heq
    have he := (S_eq_eta_iff hr hc hd hcd).mpr heq
    rw [hS] at he
    exact (ne_of_lt hlam) he
  have hlocal := rhoSquared_lt_S hr hc hd hcd hrne
  rw [hS] at hlocal
  rw [(hasDerivAt_deriv_contactGap_r
    ⟨hs, q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩⟩ hr
    (q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩)).deriv]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hlocal) (mul_pos hr.1 (sub_pos.mpr hr.2))

/-- The determinant of the matrix of actual partial derivatives of `(G,G_r)`
with respect to `(k,r)`. -/
def contactJacobianDet (lam s qv kv r : ℝ) : ℝ :=
  deriv (fun z => contactGap lam s qv z r) kv *
    deriv (deriv (fun z => contactGap lam s qv kv z)) r -
  deriv (fun z => contactGap lam s qv kv z) r *
    deriv (fun z => deriv (fun t => contactGap lam s qv z t) r) kv

/-- The nonzero-Jacobian calculation in Section 5, derived from genuine
supporting contacts and the strict curvature comparison. -/
theorem contactJacobianDet_neg {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    contactJacobianDet lam s (q c d s) (k c d) r < 0 := by
  rw [contactJacobianDet, contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact,
    zero_mul, sub_zero]
  apply mul_neg_of_pos_of_neg
  · apply contactGap_deriv_k_pos
    · exact q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
    · have heq : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
      rw [heq]
      exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
    · unfold k; linarith
    · exact hsr
  · exact contactGap_deriv2_r_neg_of_contact hs hr hc hd (ne_of_lt hcd) hlam
      (ne_of_gt hsr) hcap hcontact

end ContactJacobian

/-! ## The implicit function theorem and actual feasible families

用隐函数定理构造光滑变化的一族接触点和信道，并证明变化后仍满足系数约束。
-/

@[expose] public noncomputable section ContactFamily

open scoped ContDiff

/-- The explicit derivative of the contact gap with respect to its test input. -/
def contactSlope (lam s qv kv r : ℝ) : ℝ :=
  kv * (logOdds (qv + kv * (r - s)) - logOdds qv) -
    lam * (logOdds r - logOdds s)

/-- The two contact equations, parameterized by `(s,q)` and solved for `(k,r)`. -/
def contactSystem (lam : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (contactGap lam p.1.1 p.1.2 p.2.1 p.2.2,
   contactSlope lam p.1.1 p.1.2 p.2.1 p.2.2)

lemma contactSlope_eq_deriv {lam s qv kv r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    contactSlope lam s qv kv r = deriv (fun z => contactGap lam s qv kv z) r :=
  (hasDerivAt_contactGap_r lam s qv kv r hs hr hq hqr).deriv.symm

private lemma contDiffAt_D_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hfI : f x ∈ Set.Ioo (0 : ℝ) 1) (hgI : g x ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ n (fun z => D (f z) (g z)) x := by
  simp only [D, H_eq]
  fun_prop (disch := first | exact ne_of_gt hfI.1 | exact ne_of_gt hgI.1 |
    exact ne_of_gt (sub_pos.mpr hfI.2) | exact ne_of_gt (sub_pos.mpr hgI.2))

private lemma contDiffAt_logOdds_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ n f x)
    (hfI : f x ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ n (fun z => logOdds (f z)) x := by
  unfold logOdds
  exact (hf.log (ne_of_gt hfI.1)).sub
    ((contDiffAt_const.sub hf).log (ne_of_gt (sub_pos.mpr hfI.2)))

/-- Both contact equations are smooth on the interior probability domain. -/
theorem contDiffAt_contactSystem {lam s qv kv r : ℝ} {n : ℕ∞ω}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ n (contactSystem lam) ((s, qv), (kv, r)) := by
  have hS : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1) ((s,qv),(kv,r)) := by fun_prop
  have hQ : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2) ((s,qv),(kv,r)) := by fun_prop
  have hK : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1) ((s,qv),(kv,r)) := by fun_prop
  have hR : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.2) ((s,qv),(kv,r)) := by fun_prop
  have hY := hQ.add (hK.mul (hR.sub hS))
  exact ((contDiffAt_D_comp hY hQ hqr hq).sub
    (contDiffAt_const.mul (contDiffAt_D_comp hR hS hr hs))).prodMk
    ((hK.mul ((contDiffAt_logOdds_comp hY hqr).sub (contDiffAt_logOdds_comp hQ hq))).sub
      (contDiffAt_const.mul ((contDiffAt_logOdds_comp hR hr).sub (contDiffAt_logOdds_comp hS hs))))

private lemma prod_linear_decomposition (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (z : ℝ × ℝ) :
    L z = z.1 • L (1, 0) + z.2 • L (0, 1) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hz]
  simp only [map_add, map_smul]

/-- An explicit inverse for a triangular two-dimensional derivative. -/
private theorem triangular_isInvertible (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hA : (L (1, 0)).1 ≠ 0) (hZ : (L (0, 1)).1 = 0)
    (hC : (L (0, 1)).2 ≠ 0) : L.IsInvertible := by
  let A := (L (1, 0)).1
  let B := (L (1, 0)).2
  let C := (L (0, 1)).2
  let inv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((1 / A) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((1 / C) • ContinuousLinearMap.snd ℝ ℝ ℝ -
        (B / (A * C)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hL (z : ℝ × ℝ) : L z = (A * z.1, B * z.1 + C * z.2) := by
    rw [prod_linear_decomposition]
    ext <;> simp [A, B, C, hZ] <;> ring
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := inv)
  · apply ContinuousLinearMap.ext
    intro z
    change L (inv z) = z
    rw [hL]
    ext <;> simp [inv, smul_eq_mul] <;>
      field_simp [show A ≠ 0 from hA, show C ≠ 0 from hC]
    all_goals ring
  · apply ContinuousLinearMap.ext
    intro z
    change inv (L z) = z
    rw [hL]
    ext <;> simp [inv, smul_eq_mul] <;>
      field_simp [show A ≠ 0 from hA, show C ≠ 0 from hC]
    all_goals ring

lemma deriv_contactSlope_r {lam s qv kv r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z => contactSlope lam s qv kv z) r =
      deriv (deriv (fun z => contactGap lam s qv kv z)) r := by
  have hY : ContinuousAt (fun z : ℝ => qv + kv * (z - s)) r := by fun_prop
  have heq : (fun z => contactSlope lam s qv kv z) =ᶠ[nhds r]
      deriv (fun z => contactGap lam s qv kv z) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2, hY (Ioo_mem_nhds hqr.1 hqr.2)] with z hz hqz
    exact contactSlope_eq_deriv hs hz hq hqz
  exact heq.deriv_eq

/-- The unknown-coordinate derivative of the genuine two contact equations
is invertible. Its diagonal signs follow from supporting-contact geometry. -/
theorem contactSystem_partial_isInvertible {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    (fderiv ℝ (contactSystem lam) ((s, q c d s), (k c d, r)) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)).IsInvertible := by
  let qv := q c d s
  let kv := k c d
  have hq : qv ∈ Set.Ioo (0 : ℝ) 1 := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    have heq : qv + kv * (r - s) = q c d r := by dsimp [qv, kv, q]; ring
    rw [heq]
    exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hcdiff : ContDiffAt ℝ 1 (contactSystem lam) ((s,qv),(kv,r)) :=
    contDiffAt_contactSystem hs hr hq hqr
  have hf := (hcdiff.differentiableAt (by norm_num)).hasFDerivAt
  let L := fderiv ℝ (contactSystem lam) ((s,qv),(kv,r)) ∘L
    ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)
  have hkcurve : HasDerivAt (fun z : ℝ => ((s,qv),(z,r))) ((0,0),(1,0)) kv :=
    (hasDerivAt_const kv (s,qv)).prodMk ((hasDerivAt_id kv).prodMk (hasDerivAt_const kv r))
  have hrcurve : HasDerivAt (fun z : ℝ => ((s,qv),(kv,z))) ((0,0),(0,1)) r :=
    (hasDerivAt_const r (s,qv)).prodMk ((hasDerivAt_const r kv).prodMk (hasDerivAt_id r))
  have hfk : HasDerivAt (fun z => contactGap lam s qv z r) (L (1,0)).1 kv := by
    exact hf.fst.comp_hasDerivAt kv hkcurve
  have hfr : HasDerivAt (fun z => contactGap lam s qv kv z) (L (0,1)).1 r := by
    exact hf.fst.comp_hasDerivAt r hrcurve
  have hgr : HasDerivAt (fun z => contactSlope lam s qv kv z) (L (0,1)).2 r := by
    exact hf.snd.comp_hasDerivAt r hrcurve
  apply triangular_isInvertible L
  · rw [← hfk.deriv]
    exact ne_of_gt (contactGap_deriv_k_pos lam s qv kv r hq hqr
      (by dsimp [kv, k]; linarith) hsr)
  · rw [← hfr.deriv]
    exact contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact
  · rw [← hgr.deriv, deriv_contactSlope_r hs hr hq hqr]
    exact ne_of_lt (contactGap_deriv2_r_neg_of_contact hs hr hc hd (ne_of_lt hcd) hlam
      (ne_of_gt hsr) hcap hcontact)

/-- The implicit function theorem constructs a genuine local smooth family
of contacts with both marginals free. Invertibility is proved from the contact
hypotheses, not assumed. Feasibility follows separately from the open outer-
contact conditions. -/
theorem exists_smooth_contact_family {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    ∃ f : (ℝ × ℝ) → (ℝ × ℝ),
      ContDiffAt ℝ 1 f (s, q c d s) ∧
      f (s, q c d s) = (k c d, r) ∧
      ∀ᶠ p in nhds (s, q c d s),
        contactGap lam p.1 p.2 (f p).1 (f p).2 = 0 ∧
        contactSlope lam p.1 p.2 (f p).1 (f p).2 = 0 := by
  have hq := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr : q c d s + k c d * (r - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    have heq : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
    rw [heq]
    exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hcdiff : ContDiffAt ℝ 1 (contactSystem lam) ((s,q c d s),(k c d,r)) :=
    contDiffAt_contactSystem hs hr hq hqr
  have hi := contactSystem_partial_isInvertible hs hr hc hd hcd hlam hsr hcap hcontact
  let f := hcdiff.implicitFunction (by norm_num) hi
  refine ⟨f, hcdiff.contDiffAt_implicitFunction (by norm_num) hi,
    hcdiff.implicitFunction_apply_self (by norm_num) hi, ?_⟩
  have hbase : contactSystem lam ((s,q c d s),(k c d,r)) = (0,0) := by
    apply Prod.ext
    · change contactGap lam s (q c d s) (k c d) r = 0
      rw [contactGap_eq_tangent_sub ⟨hs,hq⟩, hcontact, sub_self]
    · change contactSlope lam s (q c d s) (k c d) r = 0
      rw [contactSlope_eq_deriv hs hr hq hqr]
      exact contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact
  have he := hcdiff.eventually_apply_implicitFunction (by norm_num) hi
  filter_upwards [he] with p hp
  rw [hbase] at hp
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The smooth family remains globally feasible and exactly saturates the cap.
This follows from the proved local-to-global supporting-contact theorem. -/
theorem exists_feasible_contact_family {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    ∃ f : (ℝ × ℝ) → (ℝ × ℝ),
      ContDiffAt ℝ 1 f (s, q c d s) ∧ f (s, q c d s) = (k c d, r) ∧
      ∀ᶠ p in nhds (s, q c d s),
        contactGap lam p.1 p.2 (f p).1 (f p).2 = 0 ∧
        contactSlope lam p.1 p.2 (f p).1 (f p).2 = 0 ∧
        Valid p.1 (p.2 - (f p).1 * p.1) (1 - p.2 - (f p).1 * (1 - p.1)) ∧
        S p.1 (p.2 - (f p).1 * p.1) (1 - p.2 - (f p).1 * (1 - p.1)) = lam := by
  obtain ⟨f, hf, hbase, heq⟩ := exists_smooth_contact_family hs hr hc hd hcd hlam hsr hcap hcontact
  refine ⟨f, hf, hbase, ?_⟩
  let C : (ℝ × ℝ) → ℝ := fun p => p.2 - (f p).1 * p.1
  let E : (ℝ × ℝ) → ℝ := fun p => 1 - p.2 - (f p).1 * (1 - p.1)
  have hC0 : C (s,q c d s) = c := by dsimp [C]; rw [hbase]; unfold q; ring
  have hE0 : E (s,q c d s) = d := by dsimp [E]; rw [hbase]; unfold q k; ring
  have hR0 : (f (s,q c d s)).2 = r := congrArg Prod.snd hbase
  have hfc := hf.continuousAt
  have hC : ContinuousAt C (s,q c d s) := by dsimp [C]; fun_prop
  have hE : ContinuousAt E (s,q c d s) := by dsimp [E]; fun_prop
  have hS0 : S s c d = lam :=
    S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd (ne_of_gt hsr) hcap hcontact
  have hq := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr := q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hlam0 : 0 < lam := by
    have hpos := (rhoSquared_pos hc hd (ne_of_lt hcd) hs).trans_le
      (rhoSquared_le_S ⟨⟨hs.1.le,hs.2.le⟩,⟨hc.1.le,hc.2.le⟩,⟨hd.1.le,hd.2.le⟩⟩ ⟨hs,hq⟩)
    rwa [hS0] at hpos
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd (ne_of_lt hcd) ⟨hlam0,hlam⟩
  have hpos := supporting_contacts_straddle_roots hs hr hc hd (ne_of_lt hcd)
    ha hb haroot hbroot hsr hcap hcontact
  have hsu : s < distinguishedInput c d := hpos.1.trans ha.2
  have hrv : distinguishedInput c d < r := hb.1.trans hpos.2
  have hrhos : rhoSquared c d s < lam :=
    rhoSquared_lt_of_left hc hd (ne_of_lt hcd) ha haroot ⟨hs.1.le,hpos.1⟩
  have hrhor : rhoSquared c d r < lam :=
    rhoSquared_lt_of_right hc hd (ne_of_lt hcd) hb hbroot ⟨hpos.2,hr.2.le⟩
  have hecont : ContinuousAt (fun p => eta (C p) (E p)) (s,q c d s) := by
    unfold eta
    fun_prop
  have hden : Real.sqrt (C (s,q c d s) * (1-C (s,q c d s))) +
      Real.sqrt (E (s,q c d s) * (1-E (s,q c d s))) ≠ 0 := by
    rw [hC0,hE0]
    exact ne_of_gt (add_pos (Real.sqrt_pos.mpr (mul_pos hc.1 (sub_pos.mpr hc.2)))
      (Real.sqrt_pos.mpr (mul_pos hd.1 (sub_pos.mpr hd.2))))
  have hdcont : ContinuousAt (fun p => distinguishedInput (C p) (E p)) (s,q c d s) := by
    unfold distinguishedInput
    fun_prop (disch := exact hden)
  have hrscont : ContinuousAt (fun p => rhoSquared (C p) (E p) p.1) (s,q c d s) := by
    unfold rhoSquared
    apply ContinuousAt.div
    · unfold k; fun_prop
    · unfold q k; fun_prop
    · rw [hC0,hE0]
      exact mul_ne_zero (ne_of_gt hq.1) (ne_of_gt (sub_pos.mpr hq.2))
  have hrrcont : ContinuousAt (fun p => rhoSquared (C p) (E p) (f p).2) (s,q c d s) := by
    unfold rhoSquared
    apply ContinuousAt.div
    · unfold k; fun_prop
    · unfold q k; fun_prop
    · rw [hC0,hE0,hR0]
      exact mul_ne_zero (ne_of_gt hqr.1) (ne_of_gt (sub_pos.mpr hqr.2))
  have hsEv : ∀ᶠ p : ℝ × ℝ in nhds (s,q c d s), p.1 ∈ Set.Ioo (0 : ℝ) 1 :=
    continuousAt_fst (Ioo_mem_nhds hs.1 hs.2)
  have hrEv : ∀ᶠ p in nhds (s,q c d s), (f p).2 ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hfc.snd
    simpa only [hR0] using Ioo_mem_nhds hr.1 hr.2
  have hcEv : ∀ᶠ p in nhds (s,q c d s), C p ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hC
    simpa only [hC0] using Ioo_mem_nhds hc.1 hc.2
  have hdEv : ∀ᶠ p in nhds (s,q c d s), E p ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hE
    simpa only [hE0] using Ioo_mem_nhds hd.1 hd.2
  have hcdEv : ∀ᶠ p in nhds (s,q c d s), C p + E p < 1 := by
    exact (hC.add hE).eventually_lt continuousAt_const
      (by simpa only [Pi.add_apply,hC0,hE0] using hcd)
  have hetaEv : ∀ᶠ p in nhds (s,q c d s), lam < eta (C p) (E p) := by
    exact continuousAt_const.eventually_lt hecont
      (by simpa only [hC0,hE0] using hlam)
  have hs0Ev : ∀ᶠ p in nhds (s,q c d s), p.1 < distinguishedInput (C p) (E p) :=
    continuousAt_fst.eventually_lt hdcont (by simpa only [hC0,hE0] using hsu)
  have hr0Ev : ∀ᶠ p in nhds (s,q c d s), distinguishedInput (C p) (E p) < (f p).2 :=
    hdcont.eventually_lt hfc.snd (by simpa only [hC0,hE0,hR0] using hrv)
  have hrsEv : ∀ᶠ p in nhds (s,q c d s), rhoSquared (C p) (E p) p.1 < lam := by
    exact hrscont.eventually_lt continuousAt_const
      (by simpa only [hC0,hE0] using hrhos)
  have hrrEv : ∀ᶠ p in nhds (s,q c d s), rhoSquared (C p) (E p) (f p).2 < lam := by
    exact hrrcont.eventually_lt continuousAt_const
      (by simpa only [hC0,hE0,hR0] using hrhor)
  filter_upwards [heq,hsEv,hrEv,hcEv,hdEv,hcdEv,hetaEv,hs0Ev,hr0Ev,hrsEv,hrrEv] with
    p hp hsp hrp hcp hdp hcdp hetap hs0p hr0p hrsp hrrp
  have hkid : k (C p) (E p) = (f p).1 := by dsimp [C,E,k]; ring
  have hqid : q (C p) (E p) p.1 = p.2 := by rw [q,hkid]; dsimp [C]; ring
  have hn : Nondegenerate p.1 (C p) (E p) :=
    ⟨hsp,q_mem_Ioo_of_channel hcp hdp ⟨hsp.1.le,hsp.2.le⟩⟩
  have hcontactp : entropyCurve lam (C p) (E p) (f p).2 = tangent lam p.1 (C p) (E p) (f p).2 := by
    have h := contactGap_eq_tangent_sub (lam := lam) hn (f p).2
    rw [hqid,hkid,hp.1] at h
    linarith
  have hderivp : deriv (entropyCurve lam (C p) (E p)) (f p).2 =
      deriv (entropyCurve lam (C p) (E p)) p.1 := by
    rw [deriv_entropyCurve lam _ _ _ hrp (q_mem_Ioo_of_channel hcp hdp ⟨hrp.1.le,hrp.2.le⟩),
      deriv_entropyCurve lam _ _ _ hsp hn.2]
    have h := hp.2
    unfold contactSlope logOdds at h
    have heq : q (C p) (E p) (f p).2 = p.2 + (f p).1 * ((f p).2 - p.1) := by
      rw [q,hkid]; dsimp [C]; ring
    rw [heq,hqid,hkid]
    linarith
  have hcapP := klCap_of_outer_contact_equations hcp hdp (ne_of_lt hcdp) ⟨hlam0,hetap⟩
    ⟨hsp.1,hs0p⟩ ⟨hr0p,hrp.2⟩ hrsp hrrp hcontactp hderivp
  refine ⟨hp.1,hp.2,⟨⟨hsp.1.le,hsp.2.le⟩,⟨hcp.1.le,hcp.2.le⟩,⟨hdp.1.le,hdp.2.le⟩⟩,?_⟩
  exact S_eq_of_supporting_contact hsp ⟨hrp.1.le,hrp.2.le⟩ hcp hdp
    (ne_of_gt (hs0p.trans hr0p)) hcapP hcontactp

end ContactFamily

end BinaryPairBound
