module

public import BinaryPairBound.ContactEndpoints
public import Mathlib.Analysis.Convex.Jensen

/-! # Outer bitangents are globally supporting

The outer convex branches support their tangents. On the intervening concave
branch, the gap above the same affine line is bounded below by its endpoint
values. Thus the local bitangent equations suffice for the global KL constraint.
-/

public section

open Set

namespace BinaryPairBound

lemma convexOn_tangent (lam s c d a b : ℝ) :
    ConvexOn ℝ (Icc a b) (tangent lam s c d) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy A B hA hB hAB
  apply le_of_eq
  simp only [smul_eq_mul, tangent]
  linear_combination -(entropyCurve lam c d s - deriv (entropyCurve lam c d) s * s) * hAB

/-- The two local contact equations determine equality of the entire tangent lines. -/
lemma tangent_eq_of_contact_and_deriv_eq {lam c d u v : ℝ}
    (hcontact : entropyCurve lam c d v = tangent lam u c d v)
    (hderiv : deriv (entropyCurve lam c d) v = deriv (entropyCurve lam c d) u) :
    tangent lam v c d = tangent lam u c d := by
  ext x
  unfold tangent at hcontact ⊢
  rw [hderiv, hcontact]
  ring

lemma tangent_lt_of_strictConvexOn {lam s c d x : ℝ} {domain : Set ℝ}
    (hconv : StrictConvexOn ℝ domain (entropyCurve lam c d))
    (hds : DifferentiableAt ℝ (entropyCurve lam c d) s)
    (hs : s ∈ domain) (hx : x ∈ domain) (hxs : x ≠ s) :
    tangent lam s c d x < entropyCurve lam c d x := by
  rcases lt_or_gt_of_ne hxs with hxs | hsx
  · have hh := hconv.slope_lt_deriv hx hs hxs hds
    rw [slope_def_field] at hh
    have hstrict := (div_lt_iff₀ (sub_pos.mpr hxs)).mp hh
    unfold tangent
    nlinarith
  · have hh := hconv.deriv_lt_slope hs hx hsx hds
    rw [slope_def_field] at hh
    have hstrict := (lt_div_iff₀ (sub_pos.mpr hsx)).mp hh
    unfold tangent
    nlinarith

/-- A common tangent on opposite outer branches lies strictly below the curve
at every other point, including the endpoints of the probability interval. -/
theorem outer_bitangent_strict_elsewhere {lam c d u v a b x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv : v ∈ Ioo b 1)
    (ht : tangent lam v c d = tangent lam u c d)
    (hx : x ∈ Icc (0 : ℝ) 1) (hxu : x ≠ u) (hxv : x ≠ v) :
    tangent lam u c d x < entropyCurve lam c d x := by
  have hs0 := distinguishedInput_mem_Ioo hc hd
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans (ha.2.trans hs0.2)⟩
  have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨(hs0.1.trans hb.1).trans hv.1, hv.2⟩
  have hdu := (hasDerivAt_entropyCurve lam u c d hu01
    (q_mem_Ioo_of_channel hc hd ⟨hu01.1.le, hu01.2.le⟩)).differentiableAt
  have hdv := (hasDerivAt_entropyCurve lam v c d hv01
    (q_mem_Ioo_of_channel hc hd ⟨hv01.1.le, hv01.2.le⟩)).differentiableAt
  have hleft : ∀ z ∈ Icc (0 : ℝ) a, z ≠ u →
      tangent lam u c d z < entropyCurve lam c d z := by
    intro z hz hzu
    exact tangent_lt_of_strictConvexOn (strictConvexOn_entropyCurve_left hc hd hcd ha haroot)
      hdu ⟨hu.1.le, hu.2.le⟩ hz hzu
  have hright : ∀ z ∈ Icc b 1, z ≠ v →
      tangent lam u c d z < entropyCurve lam c d z := by
    intro z hz hzv
    rw [← ht]
    exact tangent_lt_of_strictConvexOn (strictConvexOn_entropyCurve_right hc hd hcd hb hbroot)
      hdv ⟨hv.1.le, hv.2.le⟩ hz hzv
  by_cases hxa : x ≤ a
  · exact hleft x ⟨hx.1, hxa⟩ hxu
  by_cases hbx : b ≤ x
  · exact hright x ⟨hbx, hx.2⟩ hxv
  have hab : a < b := ha.2.trans hb.1
  have hgapconc : ConcaveOn ℝ (Icc a b)
      (entropyCurve lam c d - tangent lam u c d) :=
    (strictConcaveOn_entropyCurve_middle hc hd hcd ha hb haroot hbroot).concaveOn.sub
      (convexOn_tangent lam u c d a b)
  have hmina := hleft a ⟨ha.1.le, le_rfl⟩ (ne_of_gt hu.2)
  have hminb := hright b ⟨le_rfl, hb.2.le⟩ (ne_of_lt hv.1)
  have hmin := hgapconc.min_le_of_mem_Icc ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    (show x ∈ Icc a b from ⟨(lt_of_not_ge hxa).le, (lt_of_not_ge hbx).le⟩)
  have hp : 0 < min ((entropyCurve lam c d - tangent lam u c d) a)
      ((entropyCurve lam c d - tangent lam u c d) b) :=
    lt_min (sub_pos.mpr hmina) (sub_pos.mpr hminb)
  exact sub_pos.mp (hp.trans_le hmin)

/-- Local common-tangent equations on the two outer branches imply the full,
globally quantified KL cap. No feasibility premise is required. -/
theorem klCap_of_outer_bitangent {lam c d u v a b : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv : v ∈ Ioo b 1)
    (ht : tangent lam v c d = tangent lam u c d) : KLCap lam u c d := by
  have hu01 : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hu.1, hu.2.trans (ha.2.trans (distinguishedInput_mem_Ioo hc hd).2)⟩
  apply (klCap_iff_supporting_tangent
    ⟨hu01, q_mem_Ioo_of_channel hc hd ⟨hu01.1.le, hu01.2.le⟩⟩).mpr
  intro x hx
  by_cases hxu : x = u
  · subst x
    simp [tangent]
  by_cases hxv : x = v
  · subst x
    rw [← ht]
    simp [tangent]
  exact (outer_bitangent_strict_elsewhere hc hd hcd ha hb haroot hbroot hu hv ht hx hxu hxv).le

theorem outer_bitangent_contact_iff {lam c d u v a b x : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv : v ∈ Ioo b 1)
    (ht : tangent lam v c d = tangent lam u c d) (hx : x ∈ Icc (0 : ℝ) 1) :
    entropyCurve lam c d x = tangent lam u c d x ↔ x = u ∨ x = v := by
  constructor
  · intro he
    by_contra h
    push Not at h
    exact (ne_of_lt (outer_bitangent_strict_elsewhere hc hd hcd ha hb haroot hbroot
      hu hv ht hx h.1 h.2)) he.symm
  · rintro (rfl | rfl)
    · simp [tangent]
    · rw [← ht]
      simp [tangent]

/-- A root-free version whose hypotheses are all strict local inequalities.
This is suitable for transporting feasibility along a nearby common-tangent family. -/
theorem klCap_of_outer_bitangent_local {lam c d u v : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hlam : lam ∈ Ioo (0 : ℝ) (eta c d))
    (hu : u ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hv : v ∈ Ioo (distinguishedInput c d) 1)
    (hru : rhoSquared c d u < lam) (hrv : rhoSquared c d v < lam)
    (ht : tangent lam v c d = tangent lam u c d) : KLCap lam u c d := by
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd hcd hlam
  have hua : u < a := by
    by_contra h
    have hh := (rhoSquared_strictMonoOn hc hd hcd).monotoneOn
      ⟨ha.1.le, ha.2.le⟩ ⟨hu.1.le, hu.2.le⟩ (le_of_not_gt h)
    rw [haroot] at hh
    linarith
  have hbv : b < v := by
    by_contra h
    have hh := (rhoSquared_strictAntiOn hc hd hcd).antitoneOn
      ⟨hv.1.le, hv.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (le_of_not_gt h)
    rw [hbroot] at hh
    linarith
  exact klCap_of_outer_bitangent hc hd hcd ha hb haroot hbroot ⟨hu.1, hua⟩ ⟨hbv, hv.2⟩ ht

theorem klCap_of_outer_contact_equations {lam c d u v : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hlam : lam ∈ Ioo (0 : ℝ) (eta c d))
    (hu : u ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hv : v ∈ Ioo (distinguishedInput c d) 1)
    (hru : rhoSquared c d u < lam) (hrv : rhoSquared c d v < lam)
    (hcontact : entropyCurve lam c d v = tangent lam u c d v)
    (hderiv : deriv (entropyCurve lam c d) v = deriv (entropyCurve lam c d) u) :
    KLCap lam u c d :=
  klCap_of_outer_bitangent_local hc hd hcd hlam hu hv hru hrv
    (tangent_eq_of_contact_and_deriv_eq hcontact hderiv)

lemma tangent_le_between {lam s t c d u v x : ℝ}
    (hx : x ∈ Icc u v) (huv : u < v)
    (hu : tangent lam s c d u ≤ tangent lam t c d u)
    (hv : tangent lam s c d v ≤ tangent lam t c d v) :
    tangent lam s c d x ≤ tangent lam t c d x := by
  have he : (v - u) * (tangent lam s c d x - tangent lam t c d x) =
      (v - x) * (tangent lam s c d u - tangent lam t c d u) +
      (x - u) * (tangent lam s c d v - tangent lam t c d v) := by
    unfold tangent
    ring
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.2) (sub_nonpos.mpr hu)
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hv)
  nlinarith

/-- There is no lower-supporting tangent based strictly between the two contacts. -/
theorem not_klCap_between_outer_contacts {lam c d u v a b s : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv : v ∈ Ioo b 1)
    (ht : tangent lam v c d = tangent lam u c d) (hs : s ∈ Ioo u v) :
    ¬ KLCap lam s c d := by
  intro hcap
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩
  have hsupp := (klCap_iff_supporting_tangent
    ⟨hs01, q_mem_Ioo_of_channel hc hd ⟨hs01.1.le, hs01.2.le⟩⟩).mp hcap
  have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, (hs.1.trans hs01.2).le⟩
  have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨(hs01.1.trans hs.2).le, hv.2.le⟩
  have hule : tangent lam s c d u ≤ tangent lam u c d u := by
    simpa [tangent] using hsupp u hu01
  have hvle : tangent lam s c d v ≤ tangent lam u c d v := by
    rw [← ht]
    simpa [tangent] using hsupp v hv01
  have hle := tangent_le_between ⟨hs.1.le, hs.2.le⟩ (hs.1.trans hs.2) hule hvle
  have hlt := outer_bitangent_strict_elsewhere hc hd hcd ha hb haroot hbroot hu hv ht
    ⟨hs01.1.le, hs01.2.le⟩ (ne_of_gt hs.1) (ne_of_lt hs.2)
  have hself : tangent lam s c d s = entropyCurve lam c d s := by simp [tangent]
  rw [hself] at hle
  exact (not_le_of_gt hlt) hle

/-- There is at most one common tangent joining the two outer convex branches,
and both of its contact points are uniquely determined. -/
theorem outer_bitangent_unique {lam c d u v u' v' a b : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (ha : a ∈ Ioo (0 : ℝ) (distinguishedInput c d))
    (hb : b ∈ Ioo (distinguishedInput c d) 1)
    (haroot : rhoSquared c d a = lam) (hbroot : rhoSquared c d b = lam)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv : v ∈ Ioo b 1)
    (hu' : u' ∈ Ioo (0 : ℝ) a) (hv' : v' ∈ Ioo b 1)
    (ht : tangent lam v c d = tangent lam u c d)
    (ht' : tangent lam v' c d = tangent lam u' c d) : u = u' ∧ v = v' := by
  have hab : a < b := ha.2.trans hb.1
  have huvu : u < v' := hu.2.trans (hab.trans hv'.1)
  have huv' : u' < v := hu'.2.trans (hab.trans hv.1)
  have huu : u = u' := by
    rcases lt_trichotomy u u' with hh | hh | hh
    · exact False.elim (not_klCap_between_outer_contacts hc hd hcd ha hb haroot hbroot hu hv ht
        ⟨hh, huv'⟩ (klCap_of_outer_bitangent hc hd hcd ha hb haroot hbroot hu' hv' ht'))
    · exact hh
    · exact False.elim (not_klCap_between_outer_contacts hc hd hcd ha hb haroot hbroot hu' hv' ht'
        ⟨hh, huvu⟩ (klCap_of_outer_bitangent hc hd hcd ha hb haroot hbroot hu hv ht))
  refine ⟨huu, ?_⟩
  have hv'01 : v' ∈ Icc (0 : ℝ) 1 := ⟨(hu.1.trans huvu).le, hv'.2.le⟩
  have hcontact : entropyCurve lam c d v' = tangent lam u c d v' := by
    rw [huu, ← ht']
    simp [tangent]
  rcases (outer_bitangent_contact_iff hc hd hcd ha hb haroot hbroot hu hv ht hv'01).mp hcontact with he | he
  · exact False.elim ((ne_of_lt huvu) he.symm)
  · exact he.symm

end BinaryPairBound
