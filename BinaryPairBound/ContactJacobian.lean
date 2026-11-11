module

public import BinaryPairBound.RatioContinuity
public import BinaryPairBound.ContactGeometry
public import BinaryPairBound.Perturbation

/-!
# Nondegeneracy of the contact equations

The partial derivatives are actual Lean derivatives. At an ordered distinct
supporting contact with cap below `eta`, the determinant in Section 5 is
strictly negative. `ContactFamily.lean` uses this nonvanishing to construct
the actual smooth implicit family and prove its feasibility.
-/

noncomputable section
@[expose] public section

namespace BinaryPairBound

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

end BinaryPairBound
