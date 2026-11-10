module

public import BinaryPairBound.Divergence

/-!
# Relabeling binary pairs

The scalar identities hold without sign assumptions on the channel slope.
The coefficient proofs compare the full sets of KL ratios, and preserve the
paper's deterministic-marginal convention.
-/

public section

namespace BinaryPairBound

theorem D_one_sub (x y : ℝ) : D (1 - x) (1 - y) = D x y := by
  simp only [D, H, Real.binEntropy_one_sub, sub_sub_cancel]
  ring

lemma q_output_flip (c d x : ℝ) : q (1 - c) (1 - d) x = 1 - q c d x := by
  unfold q k
  ring

lemma k_output_flip (c d : ℝ) : k (1 - c) (1 - d) = -k c d := by
  unfold k
  ring

lemma q_swap_one_sub (c d x : ℝ) : q d c (1 - x) = 1 - q c d x := by
  unfold q k
  ring

lemma q_swap (c d x : ℝ) : q d c x = 1 - q c d (1 - x) := by
  unfold q k
  ring

lemma k_swap (c d : ℝ) : k d c = k c d := by
  unfold k
  ring

theorem J_output_flip (s c d : ℝ) : J s (1 - c) (1 - d) = J s c d := by
  simp only [J, q_output_flip, H, Real.binEntropy_one_sub]

theorem J_simultaneous_flip (s c d : ℝ) : J (1 - s) d c = J s c d := by
  simp only [J, q_swap_one_sub, H, Real.binEntropy_one_sub, sub_sub_cancel]
  ring

lemma nondegenerate_output_flip (s c d : ℝ) :
    Nondegenerate s (1 - c) (1 - d) ↔ Nondegenerate s c d := by
  unfold Nondegenerate
  rw [q_output_flip]
  constructor <;> rintro ⟨hs, hq⟩ <;> refine ⟨hs, ?_⟩ <;>
    constructor <;> linarith [hq.1, hq.2]

lemma nondegenerate_simultaneous_flip (s c d : ℝ) :
    Nondegenerate (1 - s) d c ↔ Nondegenerate s c d := by
  unfold Nondegenerate
  rw [q_swap_one_sub]
  constructor <;> rintro ⟨hs, hq⟩ <;> constructor <;> constructor <;>
    linarith [hs.1, hs.2, hq.1, hq.2]

lemma klRatios_output_flip (s c d : ℝ) :
    klRatios s (1 - c) (1 - d) = klRatios s c d := by
  ext r
  simp only [klRatios, Set.mem_ofPred_eq, q_output_flip, D_one_sub]

theorem S_output_flip (s c d : ℝ) : S s (1 - c) (1 - d) = S s c d := by
  by_cases hn : Nondegenerate s c d
  · have hn' := (nondegenerate_output_flip s c d).mpr hn
    simp only [S, ite_eq_left hn, ite_eq_left hn', klRatios_output_flip]
  · have hn' : ¬Nondegenerate s (1 - c) (1 - d) :=
      fun h => hn ((nondegenerate_output_flip s c d).mp h)
    simp only [S, ite_eq_right hn, ite_eq_right hn']

private lemma ratio_simultaneous_flip (s c d x : ℝ) :
    D (q d c x) (q d c (1 - s)) / D x (1 - s) =
      D (q c d (1 - x)) (q c d s) / D (1 - x) s := by
  rw [q_swap_one_sub, q_swap, D_one_sub]
  have hD := D_one_sub (1 - x) s
  simp only [sub_sub_cancel] at hD
  rw [hD]

private lemma klRatios_simultaneous_flip_subset (s c d : ℝ) :
    klRatios (1 - s) d c ⊆ klRatios s c d := by
  rintro r ⟨x, hx, hxs, rfl⟩
  refine ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_, ?_⟩
  · intro h
    apply hxs
    linarith
  · exact ratio_simultaneous_flip s c d x

lemma klRatios_simultaneous_flip (s c d : ℝ) :
    klRatios (1 - s) d c = klRatios s c d := by
  apply Set.Subset.antisymm
  · exact klRatios_simultaneous_flip_subset s c d
  · simpa only [sub_sub_cancel] using klRatios_simultaneous_flip_subset (1 - s) d c

theorem S_simultaneous_flip (s c d : ℝ) : S (1 - s) d c = S s c d := by
  by_cases hn : Nondegenerate s c d
  · have hn' := (nondegenerate_simultaneous_flip s c d).mpr hn
    simp only [S, ite_eq_left hn, ite_eq_left hn', klRatios_simultaneous_flip]
  · have hn' : ¬Nondegenerate (1 - s) d c :=
      fun h => hn ((nondegenerate_simultaneous_flip s c d).mp h)
    simp only [S, ite_eq_right hn, ite_eq_right hn']

lemma valid_output_flip {s c d : ℝ} (hv : Valid s c d) :
    Valid s (1 - c) (1 - d) := by
  refine ⟨hv.1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [hv.2.1.1, hv.2.1.2, hv.2.2.1, hv.2.2.2]

lemma valid_simultaneous_flip {s c d : ℝ} (hv : Valid s c d) :
    Valid (1 - s) d c := by
  exact ⟨⟨by linarith [hv.1.2], by linarith [hv.1.1]⟩, hv.2.2, hv.2.1⟩

end BinaryPairBound
