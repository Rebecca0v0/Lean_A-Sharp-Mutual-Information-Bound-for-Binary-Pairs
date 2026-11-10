module

public import BinaryPairBound.Contraction
public import BinaryPairBound.Curvature
public import BinaryPairBound.ChannelCap
public import Mathlib.Analysis.Convex.Deriv

/-!
# The local ratio is bounded by the exact contraction coefficient

Instead of assuming a quotient limit, we use the proved supporting-tangent
characterization. A smaller cap would make the entropy curve strictly
concave in a neighborhood of its reference point, contradicting the
lower-supporting tangent there.
-/

public section

namespace BinaryPairBound

lemma continuousAt_rhoSquared {c d s : ℝ}
    (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) : ContinuousAt (rhoSquared c d) s := by
  have hq := (hasDerivAt_q c d s).continuousAt
  have hn : ContinuousAt (fun x : ℝ => (k c d)^2 * x * (1 - x)) s := by fun_prop
  have hd : ContinuousAt (fun x : ℝ => q c d x * (1 - q c d x)) s :=
    hq.mul (continuousAt_const.sub hq)
  exact hn.div hd (mul_ne_zero (ne_of_gt hqs.1) (ne_of_gt (sub_pos.mpr hqs.2)))

/-- The local expression in (4.2) cannot exceed the distribution-dependent
KL coefficient. No differentiability or quotient-limit assumption is added. -/
theorem rhoSquared_le_S {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) : rhoSquared c d s ≤ S s c d := by
  by_contra h
  have hlt : S s c d < rhoSquared c d s := lt_of_not_ge h
  have hi : ∀ᶠ x in nhds s, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhds hn.1.1 hn.1.2
  have ho : ∀ᶠ x in nhds s, q c d x ∈ Set.Ioo (0 : ℝ) 1 :=
    (hasDerivAt_q c d s).continuousAt (Ioo_mem_nhds hn.2.1 hn.2.2)
  have hr : ∀ᶠ x in nhds s, S s c d < rhoSquared c d x :=
    (continuousAt_rhoSquared hn.2) (Ioi_mem_nhds hlt)
  have hu : ∀ᶠ x in nhds s,
      x ∈ Set.Ioo (0 : ℝ) 1 ∧ q c d x ∈ Set.Ioo (0 : ℝ) 1 ∧
        S s c d < rhoSquared c d x := by
    filter_upwards [hi, ho, hr] with x hxi hxo hxr
    exact ⟨hxi, hxo, hxr⟩
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hsub : ∀ x ∈ Set.Icc s (s + eps / 2),
      x ∈ Set.Ioo (0 : ℝ) 1 ∧ q c d x ∈ Set.Ioo (0 : ℝ) 1 ∧
        S s c d < rhoSquared c d x := by
    intro x hx
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hf : Continuous (entropyCurve (S s c d) c d) := by
    unfold entropyCurve q k
    fun_prop
  have hconc : StrictConcaveOn ℝ (Set.Icc s (s + eps / 2))
      (entropyCurve (S s c d) c d) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hf.continuousOn
    intro x hx
    have hx' := hsub x (interior_subset hx)
    change deriv (deriv (entropyCurve (S s c d) c d)) x < 0
    rw [deriv2_entropyCurve hx'.1 hx'.2.1]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hx'.2.2)
      (mul_pos hx'.1.1 (sub_pos.mpr hx'.1.2))
  have hsb : s < s + eps / 2 := by linarith
  have hsI : s ∈ Set.Icc s (s + eps / 2) := ⟨le_rfl, hsb.le⟩
  have hbI : s + eps / 2 ∈ Set.Icc s (s + eps / 2) := ⟨hsb.le, le_rfl⟩
  have hsec := hconc.slope_lt_deriv hsI hbI hsb
    (hasDerivAt_entropyCurve (S s c d) s c d hn.1 hn.2).differentiableAt
  rw [slope_def_field] at hsec
  have hstrict := (div_lt_iff₀ (sub_pos.mpr hsb)).1 hsec
  have hbprob := (hsub (s + eps / 2) hbI).1
  have hsupp := (S_le_iff_supporting_tangent hv hn).1 le_rfl
    (s + eps / 2) ⟨hbprob.1.le, hbprob.2.le⟩
  unfold tangent at hsupp
  linarith

/-- At the distinguished input, the exact distribution-dependent coefficient
attains the channel-wide expression in equation (4.4). -/
theorem S_distinguishedInput_eq_eta {c d : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d ≠ 1) : S (distinguishedInput c d) c d = eta c d := by
  have hs := distinguishedInput_mem_Ioo hc hd
  have hsc : distinguishedInput c d ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hv : Valid (distinguishedInput c d) c d :=
    ⟨hsc, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate (distinguishedInput c d) c d :=
    ⟨hs, q_mem_Ioo_of_channel hc hd hsc⟩
  apply le_antisymm (S_le_eta hsc hc hd)
  rw [← rhoSquared_distinguishedInput hc hd hcd]
  exact rhoSquared_le_S hv hn

end BinaryPairBound
