# BinaryPairBound

Lean formalization of Qianmian Guo, *A Sharp Mutual Information Bound for
Binary Pairs*, arXiv:2611.02392v1 (2 November 2026).

The mathematical content is organized into four parts, in reading order:

1. **Definitions and parametrization:** connect ordinary probability definitions
   to the paper's parameters and the quantities used in Lean.
2. **Theorem 2.1:** prove the main bound and its complete equality classification.
3. **Section 10 corollaries:** prove the bounds for Boolean functions of IID samples.
4. **Directionality of the contraction coefficient:** prove the two-direction
   bounds and attainment results discussed alongside the paper's future research question.

## 1. Standard probability definitions and the paper's parameters

Start with any two measurable binary random variables $W,Z$ on an arbitrary
probability space. The project constructs their actual joint probabilities
$p_{ab}=\Pr(W=a,Z=b)$ and connects them to the following parameters:

| Ordinary probability quantity | Paper / Lean parameter |
|---|---|
| Input-one probability $\Pr(W=1)$ | $s$ |
| Conditional probability $\Pr(Z=1\mid W=0)$ | $c$ |
| Conditional probability $\Pr(Z=0\mid W=1)$ | $d$ |
| Channel slope | $k=1-c-d$ |
| Output-one probability $\Pr(Z=1)$ | $q(s)=c+ks$ |

When a conditioning event has probability zero, its conditional parameter is
set to zero. The project proves that these parameters recover all four joint
probabilities, including those cases:

```math
\begin{pmatrix}p_{00}&p_{01}\\p_{10}&p_{11}\end{pmatrix}
=\begin{pmatrix}(1-s)(1-c)&(1-s)c\\sd&s(1-d)\end{pmatrix}.
```

It then proves the correspondence between the usual mathematical quantities
and the scalar expressions used in the main proof:

| Mathematical quantity or condition | Corresponding scalar expression |
|---|---|
| Shannon mutual information $I(W;Z)$ | $J(s,c,d)=H(q(s))-(1-s)H(c)-sH(d)$ |
| Directed KL contraction coefficient $s^{\ast}(W;Z)$ | $S(s,c,d)$ |
| Independence of $W$ and $Z$ | $s=0$ or $s=1$ or $c+d=1$ |
| Doubly symmetric binary source (DSBS) | $s=1/2$ and $c=d$ |

Here $H$ is binary entropy in nats. Independence of random variables is
mathlib's standard `IndepFun`; the DSBS condition is equality of opposite
joint probabilities: $p_{00}=p_{11}$ and $p_{01}=p_{10}$.

**Usual definition under full support.** First take a finite input alphabet
on which $P(x)>0$ for every input symbol $x$. This is called **full support**.
The original [AGKN paper, pp. 1–2](https://arxiv.org/pdf/1304.6133) assumes
positive marginal probabilities before giving its definition of the coefficient.
For a fixed channel $K$, the usual definition in this setting is

```math
s^{\ast}(P,K)=\sup_{Q\ne P}\frac{D(QK\Vert PK)}{D(Q\Vert P)}.
```

The supremum is over all probability laws $Q$ on the same input alphabet
other than $P$. Here $PK$ and $QK$ are the output laws through the same channel.
Full support makes $D(Q\Vert P)$ finite, and $Q\ne P$ makes it positive.
In the paper's binary setting, $P=(1-s,s)$ has full support when $0<s<1$;
writing $Q=(1-x,x)$ turns $Q\ne P$ into precisely $x\ne s$ in equation (2.2).
Deterministic input or output is treated separately, with coefficient zero.

The exclusion of $Q=P$ is now verified explicitly in
[FiniteKLStandard.lean](BinaryPairBound/FiniteKLStandard.lean).
`coefficient_eq_standardKLCoefficient` proves equality with a definition that
excludes the unchanged input and assigns zero when no alternative exists.
`coefficient_eq_sup_KL_ne_of_fullSupport` gives the displayed formula when
the reference has full support and an alternative input law exists.

**Connection to the paper's parameters.** For binary input and output,
`FiniteInfo.coefficient_binary` proves that the coefficient used by the
finite-alphabet part of the project equals the paper's $S(s,c,d)$.
The implementation conventions behind this connection are described below.

<details>
<summary>Implementation notes: support restrictions and the extra zero test</summary>

**Internal formulation.** `FiniteInfo.coefficient` is defined using entropy
ratios of nonnegative functions. The theorem `coefficient_eq_sup_KL` in
[FiniteKL.lean](BinaryPairBound/FiniteKL.lean) identifies it with a set of
KL ratios, using the following conventions.

**Zero-probability input symbols.** The Lean interface also allows finite
alphabets containing symbols with $P(x)=0$. In that setting it requires
$Q\ll P$, meaning $P(x)=0$ implies $Q(x)=0$, written `Supported Q P` in Lean.
This makes the KL sum finite and is equivalent to taking alternative input
laws on the support of $P$. More generally, the standard definition tests
laws with $0<D(Q\Vert P)<\infty$; it allows the reference law to have zeros
([Polyanskiy–Wu, equation (5)](https://arxiv.org/pdf/1508.06025#page=5)).
On finite alphabets, this domain is exactly $Q\ll P$ and $Q\ne P$.
`relativeEntropy_pos_iff` proves that, under the support condition, the KL
denominator is positive exactly when $Q\ne P$; `coefficient_eq_sup_positive_KL`
gives the corresponding supremum formula when alternatives exist.
Under the full-support assumption above, every
$Q$ automatically satisfies this condition: it removes no candidate from the
displayed definition. The current implementation uses real-valued KL sums;
it does not interpret unsupported alternatives whose ordinary KL is infinite.

**The unchanged input law.** The usual definition above excludes $Q=P$.
Substituting it anyway would give

```math
\frac{D(PK\Vert PK)}{D(P\Vert P)}=\frac{0}{0},
```

which is undefined in ordinary arithmetic. The internal set of test ratios
includes this extra test, and Lean's real division assigns it zero.
`probabilityRatios_eq_insert_standard` proves that the old test set is exactly
the new test set with zero inserted. Boundedness and nonnegativity then prove
that deleting this extra test preserves the coefficient. If there is no
supported alternative $Q\ne P$, the standard definition explicitly returns
zero; `coefficient_eq_zero_of_pointMass` proves this for every deterministic
input and every channel. These steps are Lean proofs, including all the
zero-probability cases.

</details>

**Lean entry points** (names below are in the `BinaryPairBound` namespace):

| Correspondence | File and declarations |
|---|---|
| Joint probabilities, parameters, entropy, and equality conditions | [BinaryLaw.lean](BinaryPairBound/BinaryLaw.lean): `BinaryLaw.mass00`–`BinaryLaw.mass11`, `BinaryLaw.mutualInfo_eq`, `BinaryLaw.independent_iff`, `BinaryLaw.dsbs_iff` |
| Actual random variables and standard independence | [RandomVariables.lean](BinaryPairBound/RandomVariables.lean): `binaryLaw`, `binaryLaw.independent_iff`, `binaryMutualInfo_eq_entropy`, `binaryContraction_eq_coefficient` |
| Internal entropy and supported KL ratios | [FiniteKL.lean](BinaryPairBound/FiniteKL.lean): `FiniteInfo.coefficient_eq_sup_KL` |
| Standard coefficient excluding the unchanged law | [FiniteKLStandard.lean](BinaryPairBound/FiniteKLStandard.lean): `FiniteInfo.coefficient_eq_standardKLCoefficient`, `FiniteInfo.coefficient_eq_sup_KL_ne_of_fullSupport` |
| Positive KL denominator and deterministic inputs | [FiniteKLStandard.lean](BinaryPairBound/FiniteKLStandard.lean): `FiniteInfo.relativeEntropy_pos_iff`, `FiniteInfo.coefficient_eq_sup_positive_KL`, `FiniteInfo.coefficient_eq_zero_of_pointMass` |
| Binary coefficient equals the paper's $S$ | [BinaryKernel.lean](BinaryPairBound/BinaryKernel.lean): `FiniteInfo.coefficient_binary` |
| Finite joint laws and conditional channels | [FiniteJoint.lean](BinaryPairBound/FiniteJoint.lean): `FiniteInfo.joint_conditional_mass`, `FiniteInfo.jointCoefficient_default_irrel` |

## 2. Theorem 2.1: the main bound and equality cases

For every binary pair, the main result is

```math
I(W;Z)\leq\phi(s^{\ast}(W;Z)),
\qquad \phi(u)=\log 2-H\!\left(\frac{1-\sqrt{u}}{2}\right).
```

Equality holds **if and only if** the variables are independent or their joint
law is DSBS. Through the correspondences in Part 1, the scalar statement is

```math
J(s,c,d)\leq\phi(S(s,c,d)).
```

```math
J(s,c,d)=\phi(S(s,c,d))\iff
\mathrm{Independent}(s,c,d)\lor\mathrm{DSBS}(s,c,d).
```

The proof covers all $s,c,d\in[0,1]$, including deterministic marginals and
positive, zero, or negative channel slope $k=1-c-d$.

**Lean entry points:**

| Statement | File and declarations |
|---|---|
| Original theorem specification | [Specification.lean](BinaryPairBound/Specification.lean): `MainTheorem` |
| Completed scalar proof | [MainProof.lean](BinaryPairBound/MainProof.lean): `mainTheorem`, `sharp_bound`, `sharp_equality_iff` |
| Fixed-cap optimum, equation (3.1) | [MainProof.lean](BinaryPairBound/MainProof.lean): `fixed_cap_optimum` |
| Bound and equality for actual random variables | [RandomVariables.lean](BinaryPairBound/RandomVariables.lean): `binary_random_variable_bound`, `binary_random_variable_equality_iff` |

`mainTheorem : MainTheorem` has no remaining proof premise. The conditional
assembly in `Main.lean` is retained as a reusable lemma; its `MaximizersMerge`
premise is proved in `MainProof.lean`.

## 3. Section 10: corollaries for Boolean functions of IID samples

Let $(X_1,Y_1),\ldots,(X_n,Y_n)$ be independent copies of a pair $(X,Y)$ with
finite alphabets. For any **binary-valued** functions $f$ and $g$, the project proves

```math
I(f(X^n);g(Y^n))\leq\phi(s^{\ast}(X;Y)).
```

In particular, when $(X,Y)$ is a DSBS, this gives

```math
I(f(X^n);g(Y^n))\leq I(X;Y).
```

The proof combines three proved results: independent copies preserve the
contraction coefficient (tensorization, for $n\geq1$); applying $f,g$ cannot
increase it (data processing); and Theorem 2.1 bounds the mutual information
of the resulting binary pair. Tensorization and data processing are proved
within the project, including cases where some atom probabilities are zero.

These corollaries cover every $n\geq0$, with the empty sample handled as well.
They are available both for explicitly constructed finite product laws and for
measurable random variables on an arbitrary probability space satisfying the
usual IID joint-law condition.

**Lean entry points:**

| Statement | File and declarations |
|---|---|
| Finite-source bound | [Section10.lean](BinaryPairBound/Section10.lean): `FiniteInfo.iid_binary_bound`, `FiniteInfo.iid_joint_binary_bound` |
| DSBS corollary | [Section10.lean](BinaryPairBound/Section10.lean): `FiniteInfo.iid_dsbs_binary_bound`, `FiniteInfo.iid_dsbs_binary_bound_entropy` |
| Exact tensorization | [FiniteTensorization.lean](BinaryPairBound/FiniteTensorization.lean): `FiniteInfo.coefficient_power_succ` |
| Data processing | [FiniteProcessing.lean](BinaryPairBound/FiniteProcessing.lean); `FiniteInfo.iid_binary_contraction_le` in [Section10.lean](BinaryPairBound/Section10.lean) |
| IID observations on any probability space | [Section10RandomVariables.lean](BinaryPairBound/Section10RandomVariables.lean): `iid_joint_random_variable_bound`, `iid_dsbs_random_variable_bound_source` |

Boolean functions have type `(Fin n → α) → Bool`. The theorem
`FiniteInfo.iid_joint_binary_mass` verifies the actual product-law pushforward
probabilities. `HasIIDJointLaw` expresses the IID joint-atom product formula,
and `binaryLaw_iid_joint_eq` identifies the event-based law with that pushforward.

## 4. Directionality of the contraction coefficient

The paper's concluding discussion considers both directions for the same
binary pair. Write $a=s^{\ast}(W;Z)$ and $b=s^{\ast}(Z;W)$. The project proves the
following results separately from the IID corollaries above.

**Two-direction bound and equality.** Applying Theorem 2.1 in both directions gives

```math
I(W;Z)\leq\phi(\min\{a,b\}).
```

Equality holds exactly for independent pairs or DSBS.

**Strictness for unequal coefficients.** If $a\ne b$, then

```math
I(W;Z)<\phi(\min\{a,b\}).
```

**Attainment under equal prescribed coefficients.** For every $t\in[0,1]$,
there exists a DSBS with $a=b=t$ and $I(W;Z)=\phi(t)$. Thus the optimum under
these equal constraints is attained. This is an existence result; equality of
the two coefficients alone does not make every such pair an optimizer.

**Remaining research question.** The paper proposes finding the exact optimum
and its maximizers under two unequal prescribed coefficients. That problem
remains open here. The proved strict inequality rules out attaining the stated
upper bound; it does not identify the sharp replacement bound.

**Lean entry points:**

| Statement | File and declarations |
|---|---|
| Bayes reversal, minimum bound, and equality classification | [ReverseChannel.lean](BinaryPairBound/ReverseChannel.lean): `reverseS`, `bidirectional_bound`, `bidirectional_equality_iff` |
| Strictness under unequal coefficients | [ReverseChannel.lean](BinaryPairBound/ReverseChannel.lean): `bidirectional_strict_of_ne`, `prescribed_bidirectional_strict` |
| Optimum under equal prescribed coefficients | [ReverseChannel.lean](BinaryPairBound/ReverseChannel.lean): `equal_directed_cap_optimum` |
| Bounds for actual random variables in both orders | [RandomVariableDirections.lean](BinaryPairBound/RandomVariableDirections.lean): `binary_random_variable_bidirectional_bound`, `binary_random_variable_bidirectional_strict` |

## Verification

The project uses Lean **4.35.0** and mathlib **4.35.0**, pinned to mathlib
commit `56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`.
All **60 source modules** are imported by the root module and built. `Audit.lean`
contains **133 guarded axiom checks** for the scalar theorem, random-variable interface,
KL interpretation, tensorization, data processing, and Section 10 consequences.
There are no `sorry` placeholders or additional axioms. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted by the audit.

From this project directory:

```sh
./scripts/check.sh
```

This builds the project and runs the guarded audit. The last successful
output is recorded in [`verification.log`](verification.log). The individual
steps are:

```sh
./scripts/lake.sh build
./scripts/lake.sh env lean Audit.lean
```

On a fresh checkout, install Lean using the [official guide](https://lean-lang.org/install/),
then run:

```sh
./scripts/lake.sh exe cache get
./scripts/check.sh
```

Open the entire project folder in VS Code with the Lean 4 extension.
The wrapper uses `.tooling/elan` when a project-local installation exists;
otherwise it uses the normal `lake` installation. Compiler/dependency caches
are excluded from version control. No global shell settings are changed.

## Theorem 2.1 proof map

The modules below develop the scalar proof in Part 2. Entry points for the
definition correspondences, IID corollaries, and directional results are listed
in Parts 1, 3, and 4 respectively.

| Paper step | Main modules |
|---|---|
| Definitions, KL identities, equation (4.1) | `Definitions`, `Entropy`, `TangentGap`, `Divergence` |
| Exact coefficient, endpoints, relabeling | `Contraction`, `Information`, `Endpoints`, `Symmetry` |
| Curvature and diagonal ratio | `Curvature`, `ChannelCap`, `LocalCoefficient`, `RatioContinuity` |
| Joint continuity and compact maximizers | `JointRatioContinuity`, `Compactness`, `Optimization` |
| Distinct contacts and global support | `ContactGeometry`, `ContactEndpoints`, `ContactFeasibility` |
| Smooth feasible contact family | `DivergenceCalculus`, `Perturbation`, `ContactJacobian`, `ContactFamily` |
| Both strict information-derivative signs | `InformationPerturbation`, `Hyperbolic`, `ContactMonotonicity`, `ContactSymmetry`, `ReflectedSign`, `ContactPlacement`, `OutputDirection`, `ContactSigns` |
| Boundary formula, continuation, strict improvement | `BoundaryCoefficient`, `BoundaryContinuation`, `BoundaryImprovement` |
| Cap saturation and maximizers merge | `CapSaturation`, `MaximizerVariations`, `InteriorMaximizer`, `MainProof` |
| Scalar entropy inequalities and merging bound | `ScalarEntropy`, `Merging`, `MergingSharp` |
| DSBS attainment and final assembly | `SymmetricSource`, `Reduction`, `Specification`, `Main`, `MainProof` |

The [proof blueprint](blueprint.md) records the dependencies and the
alternative arguments used in the formal proof.

## Scope and conventions

- `H` is mathlib's binary entropy in nats.
- `D x y` is finite Bernoulli KL for `x ∈ [0,1]` and `y ∈ (0,1)`.
  Its total real extension is not extended-real KL at deterministic reference
  distributions. All relevant uses supply the required domain hypotheses.
- `S` is the distribution-dependent supremum from equation (2.2), with zero
  for deterministic input or output. Its finiteness, domain bounds,
  supporting-tangent characterization, and required continuity are proved.
- Independence includes deterministic inputs. DSBS means `s=1/2 ∧ c=d`,
  with crossover probability anywhere in `[0,1]`.
- Binary random variables take values in `Bool`; the sample space and its
  probability measure are arbitrary. Independence is mathlib's `IndepFun`.
- Finite-alphabet KL tests are required to be absolutely continuous with
  respect to the reference input law (`Supported`). `FiniteKLStandard` proves
  that excluding the unchanged law gives the same coefficient, with an explicit
  zero value for an empty test set. Deterministic sources have coefficient zero.
- Arbitrary finite joint laws are reconstructed from their marginal and
  conditional channel. Choices on null input atoms do not affect the coefficient.
- Contact existence is proved at the actual cap `S(s)` for every nonmerging
  interior source, which is sufficient for the main theorem. A separate
  arbitrary-cap formulation of every assertion in Lemma 4.1 is not claimed.

Source PDF SHA-256:
`dae0f9de685a17492b61838adb0ae72a1a344b518c4456bf55584328614dbe22`.
The PDF and synced project reference files are unchanged.
