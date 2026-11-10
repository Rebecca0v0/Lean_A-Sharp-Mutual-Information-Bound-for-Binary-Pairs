module

public import BinaryPairBound.DivergenceCalculus

/-!
# Derivatives of the contact equation

These are the partial derivatives used in Section 5 and Appendix C.
They do not assert existence of an implicit contact family or its feasibility.
-/

noncomputable section

@[expose] public section

namespace BinaryPairBound

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

end BinaryPairBound
