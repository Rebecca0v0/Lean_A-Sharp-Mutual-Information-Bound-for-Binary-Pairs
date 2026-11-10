module

public import BinaryPairBound.Divergence

/-!
# Contraction coefficient and supporting tangents

The coefficient is the distribution-dependent supremum from equation (2.2).
The results below connect the exact coefficient to the universal KL cap and
then to the lower-supporting tangent condition of Section 4.1.
-/

public section

namespace BinaryPairBound

lemma klRatios_nonempty {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (klRatios s c d).Nonempty := by
  refine ⟨D (q c d 0) (q c d s) / D 0 s, 0, ?_, ne_of_lt hs.1, rfl⟩
  exact ⟨le_rfl, zero_le_one⟩

lemma S_eq_sSup {s c d : ℝ} (hn : Nondegenerate s c d) :
    S s c d = sSup (klRatios s c d) := by
  simp [S, hn]

lemma S_eq_zero_of_not_nondegenerate {s c d : ℝ} (hn : ¬Nondegenerate s c d) :
    S s c d = 0 := by
  simp [S, hn]

lemma ratio_le_S_of_bddAbove {s c d x : ℝ}
    (hn : Nondegenerate s c d) (hb : BddAbove (klRatios s c d))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxs : x ≠ s) :
    D (q c d x) (q c d s) / D x s ≤ S s c d := by
  rw [S_eq_sSup hn]
  exact le_csSup hb ⟨x, hx, hxs, rfl⟩

lemma S_le_iff_ratios_le_of_bddAbove {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hb : BddAbove (klRatios s c d)) :
    S s c d ≤ lam ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ s →
        D (q c d x) (q c d s) / D x s ≤ lam := by
  rw [S_eq_sSup hn, csSup_le_iff hb (klRatios_nonempty hn.1)]
  constructor
  · intro h x hx hxs
    exact h _ ⟨x, hx, hxs, rfl⟩
  · rintro h r ⟨x, hx, hxs, rfl⟩
    exact h x hx hxs

lemma klRatios_bddAbove_of_klCap {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hcap : KLCap lam s c d) :
    BddAbove (klRatios s c d) := by
  refine ⟨lam, ?_⟩
  rintro r ⟨x, hx, hxs, rfl⟩
  exact (div_le_iff₀ (D_pos hx hn.1 hxs)).2 (hcap x hx)

lemma S_le_of_klCap {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hcap : KLCap lam s c d) :
    S s c d ≤ lam := by
  rw [S_eq_sSup hn]
  apply csSup_le (klRatios_nonempty hn.1)
  rintro r ⟨x, hx, hxs, rfl⟩
  exact (div_le_iff₀ (D_pos hx hn.1 hxs)).2 (hcap x hx)

lemma S_le_iff_klCap_of_bddAbove {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hb : BddAbove (klRatios s c d)) :
    S s c d ≤ lam ↔ KLCap lam s c d := by
  constructor
  · intro h x hx
    by_cases hxs : x = s
    · subst x
      simp only [D_self, mul_zero, le_refl]
    · apply (div_le_iff₀ (D_pos hx hn.1 hxs)).1
      exact (ratio_le_S_of_bddAbove hn hb hx hxs).trans h
  · exact S_le_of_klCap hn

lemma klCap_one {s c d : ℝ} (hv : Valid s c d) (hn : Nondegenerate s c d) :
    KLCap 1 s c d := by
  intro x hx
  simpa only [one_mul] using D_dataProcessing hv.2.1 hv.2.2 hx hn.1 hn.2

/-- The ratio set has the genuine upper bound `1`, by binary data processing. -/
theorem klRatios_bddAbove {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) : BddAbove (klRatios s c d) :=
  klRatios_bddAbove_of_klCap hn (klCap_one hv hn)

theorem S_nonneg {s c d : ℝ} (hv : Valid s c d) : 0 ≤ S s c d := by
  by_cases hn : Nondegenerate s c d
  · rw [S_eq_sSup hn]
    apply Real.sSup_nonneg
    rintro r ⟨x, hx, hxs, rfl⟩
    exact div_nonneg (D_nonneg (q_mem_Icc c d x hv.2.1 hv.2.2 hx) hn.2)
      (D_nonneg hx hn.1)
  · rw [S_eq_zero_of_not_nondegenerate hn]

theorem S_le_one {s c d : ℝ} (hv : Valid s c d) : S s c d ≤ 1 := by
  by_cases hn : Nondegenerate s c d
  · exact S_le_of_klCap hn (klCap_one hv hn)
  · rw [S_eq_zero_of_not_nondegenerate hn]
    exact zero_le_one

theorem S_mem_Icc {s c d : ℝ} (hv : Valid s c d) : S s c d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨S_nonneg hv, S_le_one hv⟩

theorem ratio_le_S {s c d x : ℝ} (hv : Valid s c d) (hn : Nondegenerate s c d)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxs : x ≠ s) :
    D (q c d x) (q c d s) / D x s ≤ S s c d :=
  ratio_le_S_of_bddAbove hn (klRatios_bddAbove hv hn) hx hxs

/-- The exact supremum coefficient is at most a cap iff every test input
satisfies its KL inequality. There is no assumed bound on the supremum. -/
theorem S_le_iff_klCap {lam s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) : S s c d ≤ lam ↔ KLCap lam s c d :=
  S_le_iff_klCap_of_bddAbove hn (klRatios_bddAbove hv hn)

theorem klCap_S {s c d : ℝ} (hv : Valid s c d) (hn : Nondegenerate s c d) :
    KLCap (S s c d) s c d :=
  (S_le_iff_klCap hv hn).1 le_rfl

/-- Independent inputs have zero coefficient, including deterministic inputs. -/
theorem S_eq_zero_of_independent {s c d : ℝ} (hi : Independent s c d) :
    S s c d = 0 := by
  rcases hi with hs | hs | hcd
  · subst s
    simp [S, Nondegenerate]
  · subst s
    simp [S, Nondegenerate]
  · by_cases hn : Nondegenerate s c d
    · have hk : k c d = 0 := by unfold k; linarith
      have hr : klRatios s c d = {0} := by
        ext r
        constructor
        · rintro ⟨x, hx, hxs, rfl⟩
          simp [q, hk]
        · intro hr
          have hr0 : r = 0 := hr
          subst r
          refine ⟨0, ⟨le_rfl, zero_le_one⟩, ne_of_lt hn.1.1, ?_⟩
          simp [q, hk]
      rw [S_eq_sSup hn, hr]
      simp
    · exact S_eq_zero_of_not_nondegenerate hn

/-- The universal KL inequality is exactly the lower-supporting tangent
condition. This part does not need a sign restriction on the cap. -/
theorem klCap_iff_supporting_tangent {lam s c d : ℝ}
    (hn : Nondegenerate s c d) :
    KLCap lam s c d ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, tangent lam s c d x ≤ entropyCurve lam c d x := by
  constructor
  · intro h x hx
    have hcap := h x hx
    have hgap := equation_4_1 lam s c d x hn.1 hn.2
    linarith
  · intro h x hx
    have hsupp := h x hx
    have hgap := equation_4_1 lam s c d x hn.1 hn.2
    linarith

/-- Section 4.1: the distribution-dependent contraction cap is equivalent
to the tangent being lower supporting on the entire probability interval. -/
theorem S_le_iff_supporting_tangent {lam s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) :
    S s c d ≤ lam ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, tangent lam s c d x ≤ entropyCurve lam c d x :=
  (S_le_iff_klCap hv hn).trans (klCap_iff_supporting_tangent hn)

end BinaryPairBound
