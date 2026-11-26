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

If $\Pr(W=0)=0$, the conditional parameter $c$ is set to zero; if
$\Pr(W=1)=0$, $d$ is set to zero. These are choices for conditioning events
that never occur. They do not affect the joint law, because the corresponding
row is multiplied by zero. The project proves the following formula in all
cases:

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

**KL contraction coefficient.** For a finite input law $P$ and a channel
$K$, use the definition ([Polyanskiy–Wu, equation (5)](https://arxiv.org/pdf/1508.06025#page=5))

```math
s^{\ast}(P,K)
=\sup_{Q:\,0\lt D(Q\Vert P)\lt\infty}
\frac{D(QK\Vert PK)}{D(Q\Vert P)}.
```

Here Q ranges over probability laws on the same input alphabet.
**If no Q satisfies the constraint, set $s^{\ast}(P,K)=0$.**

Lean proves that this coefficient equals the paper's $S(s,c,d)$ under the
binary parametrization above, including deterministic cases.

On finite alphabets, $0\lt D(Q\Vert P)\lt\infty$ is encoded by
`Supported Q P` and `Q ≠ P`. `standardKLCoefficient` uses this domain and an
explicit zero value when it is empty. Its equality with the internal
coefficient used by the proofs is verified in `FiniteKLStandard`.

**Lean entry points** (names below are in the `BinaryPairBound` namespace):

| Statement | File and declarations |
|---|---|
| The constructed joint law has $p_{ab}=\Pr(W=a,Z=b)$ | [RandomVariables.lean](BinaryPairBound/RandomVariables.lean): `binaryLaw` |
| The parameters $s,c,d$ reproduce the displayed joint-probability matrix | [BinaryLaw.lean](BinaryPairBound/BinaryLaw.lean): `BinaryLaw.mass00`, `BinaryLaw.mass01`, `BinaryLaw.mass10`, `BinaryLaw.mass11` |
| $I(W;Z)=J(s,c,d)$ | [BinaryLaw.lean](BinaryPairBound/BinaryLaw.lean): `BinaryLaw.mutualInfo_eq` |
| The KL-ratio definition above gives $s^{\ast}(W;Z)=S(s,c,d)$ | [FiniteKLStandard.lean](BinaryPairBound/FiniteKLStandard.lean): `FiniteInfo.coefficient_eq_standardKLCoefficient`; [BinaryKernel.lean](BinaryPairBound/BinaryKernel.lean): `FiniteInfo.coefficient_binary` |
| $W,Z$ are independent iff $s=0$, $s=1$, or $c+d=1$ | [BinaryLaw.lean](BinaryPairBound/BinaryLaw.lean): `BinaryLaw.independent_iff`; [RandomVariables.lean](BinaryPairBound/RandomVariables.lean): `binaryLaw.independent_iff` |
| The joint law is DSBS iff $s=1/2$ and $c=d$ | [BinaryLaw.lean](BinaryPairBound/BinaryLaw.lean): `BinaryLaw.dsbs_iff` |

## 2. Theorem 2.1: the main bound and equality cases

Theorem 2.1 proves the bound in equation (1.1) for every binary pair:

```math
I(W;Z)\leq\phi(s^{\ast}(W;Z)),
\qquad \phi(u)=\log 2-H\!\left(\frac{1-\sqrt{u}}{2}\right).
```

Equality holds **if and only if** the variables are independent or their joint
law is DSBS. Using the correspondences in Part 1, the same theorem written in
the parameters $s,c,d$ is

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

The first two rows give the parameter form; the next two give the same result
for measurable binary random variables on any probability space.

| Statement | File and declarations |
|---|---|
| Theorem 2.1, bound: $J(s,c,d)\leq\phi(S(s,c,d))$ | [MainProof.lean](BinaryPairBound/MainProof.lean): `sharp_bound` |
| Theorem 2.1, equality: $J(s,c,d)=\phi(S(s,c,d))$ iff independence or DSBS | [MainProof.lean](BinaryPairBound/MainProof.lean): `sharp_equality_iff` |
| Equation (1.1): $I(W;Z)\leq\phi(s^{\ast}(W;Z))$ | [RandomVariables.lean](BinaryPairBound/RandomVariables.lean): `binary_random_variable_bound` |
| Equality in (1.1): $I(W;Z)=\phi(s^{\ast}(W;Z))$ iff $W,Z$ are independent or DSBS | [RandomVariables.lean](BinaryPairBound/RandomVariables.lean): `binary_random_variable_equality_iff` |
| Equation (3.1): the maximum of $J$ under $S\leq\lambda$ is $\phi(\lambda)$, for $\lambda\in[0,1]$ | [MainProof.lean](BinaryPairBound/MainProof.lean): `fixed_cap_optimum` |

`MainTheorem` in [Specification.lean](BinaryPairBound/Specification.lean)
names the first two statements together; `mainTheorem` in
[MainProof.lean](BinaryPairBound/MainProof.lean) is their proof.

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

**Lean entry points:**

The first two rows are the corollaries; the last two are the coefficient
properties used to prove them.

| Statement and meaning | File and declarations |
|---|---|
| **General finite source:** $I(f(X^n);g(Y^n))\leq\phi(s^{\ast}(X;Y))$. The bound depends only on the joint distribution of $(X,Y)$ and holds for every sample size and every binary-valued $f,g$. | [Section10.lean](BinaryPairBound/Section10.lean): `FiniteInfo.iid_binary_bound`, `FiniteInfo.iid_joint_binary_bound` |
| **DSBS source:** $I(f(X^n);g(Y^n))\leq I(X;Y)$. The two binary outputs share at most as much mutual information as one original source pair. | [Section10.lean](BinaryPairBound/Section10.lean): `FiniteInfo.iid_dsbs_binary_bound`, `FiniteInfo.iid_dsbs_binary_bound_entropy` |
| **Tensorization:** $s^{\ast}(X^n;Y^n)=s^{\ast}(X;Y)$ for $n\geq1$. Independent repetition leaves the directed KL contraction coefficient unchanged. | [FiniteTensorization.lean](BinaryPairBound/FiniteTensorization.lean): `FiniteInfo.coefficient_power_succ` |
| **Data processing:** $s^{\ast}(f(X^n);g(Y^n))\leq s^{\ast}(X^n;Y^n)$. Applying $f$ and $g$ separately cannot increase the directed KL contraction coefficient. | [FiniteProcessing.lean](BinaryPairBound/FiniteProcessing.lean): `FiniteInfo.processedLaw_contraction_le` |

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

## 5. Verification

The project uses Lean **4.35.0** and mathlib **4.35.0**, pinned to mathlib
commit `56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`.
All **61 source modules** are imported by the root module and built. `Audit.lean`
contains **143 guarded axiom checks** for the scalar theorem, random-variable interface,
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
- The general coefficient allows zero probabilities in $P$ and directly
  requires `Supported Q P` and $Q\ne P$. It is defined to be zero when no
  candidate exists, including deterministic inputs. `FiniteKLStandard` proves
  equality with the internal coefficient used by the existing theorems.
- `FiniteKLAGKN` provides the full-support special case, with only $Q\ne P$
  imposed on the alternative law, and proves agreement with the general coefficient.
- Arbitrary finite joint laws are reconstructed from their marginal and
  conditional channel. The default output symbol chosen on null input atoms
  does not affect the coefficient.
- Contact existence is proved at the actual cap `S(s)` for every dependent,
  nonmerging interior source, which is sufficient for the main theorem. A separate
  arbitrary-cap formulation of every assertion in Lemma 4.1 is not claimed.

Source PDF SHA-256:
`dae0f9de685a17492b61838adb0ae72a1a344b518c4456bf55584328614dbe22`.
The PDF and synced project reference files are unchanged.
