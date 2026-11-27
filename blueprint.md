# Proof blueprint

Source: Qianmian Guo, *A Sharp Mutual Information Bound for Binary Pairs*,
arXiv:2611.02392v1 (2 November 2026). Equation numbers refer to that version.

## Completed target

All intermediate results used to prove Theorem 2.1 are proved within this
project. Applying `mainTheorem` requires no additional assumptions about
those results.

## Reading the reorganized source

The source has **17 mathematical chapters**. Read a chapter for its complete
mathematical goal: its definitions, the lemmas needed for that goal, and the
final theorem are kept together. The order below is also a valid order for
reading the project dependencies.

Start with the derivation of equation (4.1) below. Then follow the main-theorem
chapters, the probability interfaces, the IID consequences, and directionality.
The theorem names have been retained, so a declaration can still be found by
searching for its existing name.

## 1. Binary entropy, KL, and the complete proof of equation (4.1)

Read [BinaryInformation.lean](BinaryPairBound/BinaryInformation.lean).
This chapter contains the parameter definitions, entropy and KL identities,
the derivative calculations, equation (4.1), and the equivalent KL cap condition.

**Goal.** For the curve and its actual tangent

```math
F_\lambda(x)=H(q(x))-\lambda H(x),
\qquad T_{\lambda,s}(x)=F_\lambda(s)+F_\lambda'(s)(x-s),
```

prove

```math
F_\lambda(x)-T_{\lambda,s}(x)
=\lambda D(x,s)-D(q(x),q(s)).
```

Here `q(c,d,x) = c + (1-c-d)x`. For the probability interpretation,
`x,s,c,d` belong to `[0,1]`, and the reference probabilities satisfy
`0 < s < 1` and `0 < q(s) < 1`.

**First identify the functions.** `H` is an abbreviation for mathlib's
`Real.binEntropy`. `H_eq` proves its logarithmic expression. `D` is defined by

```math
D(x,s)=-H(x)-x\log s-(1-x)\log(1-s).
```

`D_eq_log_ratio` proves agreement with the usual Bernoulli KL formula when
`x ∈ [0,1]` and `s ∈ (0,1)`. The endpoints `x=0,1` are included. At a
reference value `s=0` or `s=1`, this real-valued formula must not be read as
extended-real KL. The definition of `S` handles deterministic inputs and
outputs separately.

**Next prove the slopes.** `hasDerivAt_H_log` invokes mathlib's proved
`Real.hasDerivAt_binEntropy` to establish

```math
H'(s)=\log(1-s)-\log s.
```

`hasDerivAt_q` gives `q'(s)=k`, where `k=1-c-d`. The chain rule in
`hasDerivAt_entropyCurve`, followed by `deriv_entropyCurve`, gives

```math
F_\lambda'(s)
=k\bigl[\log(1-q(s))-\log q(s)\bigr]
-\lambda\bigl[\log(1-s)-\log s\bigr].
```

The definition `tangent` uses `deriv (entropyCurve lam c d) s`.
Thus this slope is proved to be the actual derivative; it is not supplied as
an extra tangent hypothesis.

**Then calculate the gap.** `entropy_tangent_gap` proves the algebraic identity

```math
H(x)-H(s)-\bigl[\log(1-s)-\log s\bigr](x-s)=-D(x,s).
```

This identity alone does not establish differentiability. The derivative
results above justify interpreting its logarithmic coefficient as a slope.

`equation_4_1` applies the identity twice: once at the output probabilities
$q(x),q(s)$, giving $-D(q(x),q(s))$, and once at $x,s$, multiplied by
$-\lambda$, giving $\lambda D(x,s)$. The relation
$q(x)-q(s)=k(x-s)$ makes their sum exactly $F_\lambda(x)-T_{\lambda,s}(x)$.

`equation_4_1_log_ratio` writes the result in the paper's logarithm-of-ratio
notation, including test inputs `0` and `1`.

**Finally connect the formula to the constraint.** The same chapter proves
KL positivity and data processing, the bounds `0 ≤ S ≤ 1`, and the cap
characterization `S_le_iff_supporting_tangent`. For valid, nondegenerate
parameters and a nonnegative cap `lambda`, the condition `S ≤ lambda` is
equivalent to

```math
D(q(x),q(s))\leq\lambda D(x,s)\quad\text{for every }x\in[0,1],
```

and hence to $F_\lambda(x)\geq T_{\lambda,s}(x)$ throughout that interval.
These are the constraint and geometry used in the later chapters.

## Theorem 2.1 proof map

The following chapters complete the scalar theorem. Each row states the
mathematical question answered in that file and names its main conclusions.

| Order | Mathematical goal | Chapter and main conclusions |
|---|---|---|
| 2 | Establish basic bounds for mutual information and `phi`; settle the coefficient endpoints and relabeling. | [InformationBounds.lean](BinaryPairBound/InformationBounds.lean): `J_eq_zero_iff_independent`, `phi_increment_le`, `S_eq_zero_iff_independent`, `sharp_equality_iff_of_S_one` |
| 3 | Determine the curve's convex and concave regions, the channel bound `eta`, and the distinguished input where the local bound is attained. | [ChannelGeometry.lean](BinaryPairBound/ChannelGeometry.lean): `S_le_eta`, `S_distinguishedInput_eq_eta`, `rhoSquared_two_roots` |
| 4 | Prove the sharp bound at the distinguished input, classify equality there, and construct DSBS examples attaining every cap. | [SharpMerging.lean](BinaryPairBound/SharpMerging.lean): `merging_sharp_bound`, `merging_sharp_eq_iff_dsbs`, `exists_sharp_cap_witness` |
| 5 | Show that mutual information attains a maximum under a prescribed coefficient cap. | [MaximizerExistence.lean](BinaryPairBound/MaximizerExistence.lean): `exists_cap_maximizer`, `exists_nontrivial_normalized_maximizer` |
| 6 | Fill in the diagonal limit of the KL ratio and prove continuity when the input and channel vary. | [CoefficientContinuity.lean](BinaryPairBound/CoefficientContinuity.lean): `tendsto_klRatio_nhdsNE`, `exists_extendedRatio_eq_S`, `continuousAt_S_comp` |
| 7 | Locate distinct interior contact points and show that the outer common tangent supplies the global KL constraint. | [SupportingContacts.lean](BinaryPairBound/SupportingContacts.lean): `exists_ordered_interior_contacts`, `klCap_of_outer_bitangent_local`, `outer_bitangent_unique` |
| 8 | Construct a smooth family of channels and contact points that preserves the constraint. | [ContactFamilies.lean](BinaryPairBound/ContactFamilies.lean): `contactSystem_partial_isInvertible`, `exists_feasible_contact_family` |
| 9 | Prove that an appropriate change along this family has a strictly signed information derivative. The scalar estimates and their application are together here. | [ContactSigns.lean](BinaryPairBound/ContactSigns.lean): `informationCoords_supporting_input_curve_deriv_pos`, `informationCoords_supporting_output_curve_deriv_neg` |
| 10 | Prove that an interior maximizer uses the full cap and must have its input at the distinguished merging point. | [InteriorMaximizers.lean](BinaryPairBound/InteriorMaximizers.lean): `interior_cap_maximizer_saturates`, `interior_cap_maximizer_distinguishedInput` |
| 11 | Calculate the boundary coefficient, continue into the interior at the same coefficient, and strictly improve mutual information. | [BoundaryImprovement.lean](BinaryPairBound/BoundaryImprovement.lean): `S_zero_right`, `existsUnique_boundary_continuation`, `boundary_improvement_zero_right` |
| 12 | Combine these results to prove Theorem 2.1, both directions of its equality classification, and the fixed-cap optimum. | [MainTheorem.lean](BinaryPairBound/MainTheorem.lean): `maximizersMerge`, `mainTheorem`, `sharp_bound`, `sharp_equality_iff`, `fixed_cap_optimum` |

The final argument is as follows. For a cap between zero and one, choose a
maximizer. The boundary improvement shows that its channel lies in the
interior. At an interior maximum, a feasible smooth variation has derivative
zero. The strict derivative signs exclude distinct contacts, so the input
must be the distinguished merging input. The bound from `SharpMerging`
therefore applies to the maximizer and hence to every point under the cap.

For equality, any source attaining the bound is itself a cap maximizer.
The same reduction and the merging equality theorem force it to be DSBS.
At coefficient zero, equality is independence; coefficient one is treated
by the entropy maximum. Relabeling covers negative channel slopes.

Maximizer existence uses closed cap sets and compactness. It does not require
the joint-continuity result proved in the following chapter.

## 13–14. Standard probability definitions and the binary parameters

Read [FiniteInformation.lean](BinaryPairBound/FiniteInformation.lean) for the
finite-alphabet definitions and their complete coefficient correspondence.
The chapter starts with laws and channels, proves the entropy contraction
facts, and identifies the internal coefficient with

```math
\sup_{Q:\,0\lt D(Q\Vert P)\lt\infty}
\frac{D(QK\Vert PK)}{D(Q\Vert P)},
```

with value zero when there is no admissible alternative. On a finite alphabet,
the constraint is encoded by `Supported Q P` and `Q ≠ P`. The main result is
`FiniteInfo.coefficient_eq_standardKLCoefficient`. The full-support AGKN
special case and the reconstruction of a channel from a joint law are in
this same chapter.

Read [BinaryRandomVariables.lean](BinaryPairBound/BinaryRandomVariables.lean)
for the complete passage from four joint probabilities to the parameters
`s,c,d`, and then to actual measurable binary random variables on an arbitrary
probability space. `BinaryLaw.mutualInfo_eq` identifies mutual information
with `J`; `FiniteInfo.coefficient_binary` identifies the finite coefficient
with `S`, including deterministic cases. The final results are
`binary_random_variable_bound` and `binary_random_variable_equality_iff`.
The latter uses mathlib's `IndepFun` and the DSBS condition on joint atoms.

## 15–16. Tensorization and Section 10

Read [Tensorization.lean](BinaryPairBound/Tensorization.lean) for the complete
product argument: log-sum and entropy convexity, a cap for independent
products, induction over IID copies, and the reverse inequality obtained by
testing a single coordinate. `FiniteInfo.coefficient_power_succ` proves exact
coefficient equality for every positive number of copies.

Read [Section10.lean](BinaryPairBound/Section10.lean) for the remaining
argument in one place. `processedLaw_contraction_le` proves that separately
applying Boolean functions does not increase the coefficient.
`iid_binary_bound` combines that fact with `Contracts.power` and Theorem 2.1:

```math
I(f(X^n);g(Y^n))\leq\phi(s^{\ast}(X;Y)).
```

The source pair may have arbitrary finite alphabets; the outputs of `f,g`
are binary. The chapter includes the DSBS consequence, the full-support
AGKN formulation, and the version for measurable IID observations on an
arbitrary probability space. `HasIIDJointLaw` states the joint-atom product
formula; `iid_joint_random_variable_bound` proves the resulting bound.
All sample sizes `n ≥ 0` and zero-mass atoms are covered.

## 17. Directionality

Read [Directionality.lean](BinaryPairBound/Directionality.lean). It constructs
the reverse binary channel, proves mutual-information symmetry, and applies
Theorem 2.1 in both directions. With `a = s*(W;Z)` and `b = s*(Z;W)`, it proves

```math
I(W;Z)\leq\phi(\min\{a,b\}).
```

Equality holds exactly for independent pairs or DSBS; if `a ≠ b`, the
inequality is strict. For each `t ∈ [0,1]`, a DSBS attains `phi(t)` with
`a=b=t`. The scalar and actual-random-variable results are in this same file.
Start with `bidirectional_equality_iff`, `bidirectional_strict_of_ne`,
`equal_directed_cap_optimum`, and `binary_random_variable_bidirectional_bound`.

The exact optimum under two unequal prescribed coefficients remains open in
this project. Strictness of the displayed bound does not determine the sharp
replacement bound.

## Verification and scope

The root [BinaryPairBound.lean](BinaryPairBound.lean) imports all 17 chapters.
[Audit.lean](Audit.lean) contains 143 guarded axiom checks. Run
`./scripts/check.sh` to build the library and execute them. See the
[README verification instructions](README.md#verification) for the pinned
versions and setup.

The contact results used by the proof are established at every dependent,
nonmerging interior source's actual cap. A separate arbitrary-cap version of
all of the paper's Lemma 4.1 is not claimed.
