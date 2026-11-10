module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar definitions for arXiv:2611.02392v1

Entropy is in nats. `D x y` represents Bernoulli KL divergence when
`x ∈ [0,1]` and `y ∈ (0,1)`. Its total real-valued extension outside that
domain is not an extended-real KL divergence. `S` handles deterministic
input/output separately, following Section 2 of the paper.
-/

noncomputable section

@[expose] public section

namespace BinaryPairBound

abbrev H : ℝ → ℝ := Real.binEntropy

/-- Cross-entropy form of Bernoulli KL, with interior reference parameter. -/
def D (x y : ℝ) : ℝ := -H x - x * Real.log y - (1 - x) * Real.log (1 - y)

/-- The channel slope. -/
def k (c d : ℝ) : ℝ := 1 - c - d

/-- Output-one probability at input-one probability `x`. -/
def q (c d x : ℝ) : ℝ := c + k c d * x

/-- All binary input/channel parameters, without a sign normalization on `k`. -/
def Valid (s c d : ℝ) : Prop :=
  s ∈ Set.Icc (0 : ℝ) 1 ∧ c ∈ Set.Icc (0 : ℝ) 1 ∧ d ∈ Set.Icc (0 : ℝ) 1

/-- Both marginal distributions have full support. -/
def Nondegenerate (s c d : ℝ) : Prop :=
  s ∈ Set.Ioo (0 : ℝ) 1 ∧ q c d s ∈ Set.Ioo (0 : ℝ) 1

/-- Mutual information, equation (2.1). -/
def J (s c d : ℝ) : ℝ := H (q c d s) - (1 - s) * H c - s * H d

/-- The set of ratios in equation (2.2), excluding the diagonal `x = s`. -/
def klRatios (s c d : ℝ) : Set ℝ :=
  {r | ∃ x ∈ Set.Icc (0 : ℝ) 1, x ≠ s ∧ r = D (q c d x) (q c d s) / D x s}

/-- Distribution-dependent contraction coefficient, with the paper's zero convention.

The nonemptiness and boundedness of `klRatios` under `Valid` and
`Nondegenerate` are outstanding blueprint obligations, not assumed facts.
-/
def S (s c d : ℝ) : ℝ := by
  classical
  exact if Nondegenerate s c d then sSup (klRatios s c d) else 0

/-- The sharp upper-bound function from Theorem 2.1. -/
def phi (u : ℝ) : ℝ := Real.log 2 - H ((1 - Real.sqrt u) / 2)

/-- Scalar independence, including deterministic inputs. -/
def Independent (s c d : ℝ) : Prop := s = 0 ∨ s = 1 ∨ c + d = 1

/-- Doubly symmetric binary source; crossover may lie anywhere in `[0,1]`. -/
def DSBS (s c d : ℝ) : Prop := s = 1 / 2 ∧ c = d

/-- An interior reference is required when interpreting this predicate as a KL cap. -/
def KLCap (lam s c d : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, D (q c d x) (q c d s) ≤ lam * D x s

/-- Entropy curve from Section 4. -/
def entropyCurve (lam c d x : ℝ) : ℝ := H (q c d x) - lam * H x

/-- The actual derivative-based tangent line at `s`, not an independently chosen slope. -/
def tangent (lam s c d x : ℝ) : ℝ :=
  entropyCurve lam c d s + deriv (entropyCurve lam c d) s * (x - s)

end BinaryPairBound
