# BinaryPairBound

Lean verification of **Theorem 2.1 on arbitrary probability spaces and the
finite-source consequences in Section 10** of
Qianmian Guo, *A Sharp Mutual Information Bound for Binary Pairs*,
arXiv:2611.02392v1 (2 November 2026).

The original scalar theorem specification is proved, including its complete
equality classification:

\[
J(s,c,d)\leq\phi(S(s,c,d)),\qquad
J(s,c,d)=\phi(S(s,c,d))\iff
\mathrm{Independent}(s,c,d)\lor\mathrm{DSBS}(s,c,d).
\]

The statement covers all `s,c,d ∈ [0,1]`, deterministic marginals, and both
signs of the channel slope. There are no `sorry` proofs or additional axioms.

The random-variable interface constructs the actual joint law of any two
measurable binary random variables on an arbitrary probability space. It proves
the same bound and characterizes equality using mathlib's `IndepFun` or a
doubly symmetric joint distribution. The finite-alphabet coefficient is proved
equal to the usual supremum of KL ratios over supported alternative input laws.

Section 10 is proved for every finite-alphabet source, every number of IID
observations, and every pair of Boolean functions:

\[
I(f(X^n);g(Y^n))\leq\phi(s^*(X;Y)).
\]

For a DSBS this gives `I(f(Xⁿ);g(Yⁿ)) ≤ I(X;Y)`. Tensorization and data
processing are proved, including zero-mass atoms; they are not supplied as
theorem assumptions. The bidirectional minimum bound, strictness when the
two directed coefficients differ, and attainment when they agree are also proved.

## Main entry points

In [`BinaryPairBound/MainProof.lean`](BinaryPairBound/MainProof.lean):

```lean
BinaryPairBound.mainTheorem : BinaryPairBound.MainTheorem
BinaryPairBound.sharp_bound
BinaryPairBound.sharp_equality_iff
BinaryPairBound.fixed_cap_optimum
```

`mainTheorem` has **no remaining proof premise**. It inhabits the original
`MainTheorem` specification. `sharp_bound` and `sharp_equality_iff` expose
its two conclusions directly; `fixed_cap_optimum` proves equation (3.1).
The former conditional assembly in `Main.lean` is retained as a reusable
lemma; its `MaximizersMerge` premise is discharged in `MainProof.lean`.

Additional entry points:

| Interface | Declarations |
|---|---|
| Arbitrary probability space | `binary_random_variable_bound`, `binary_random_variable_equality_iff` in `RandomVariables.lean` |
| Exact finite KL interpretation | `FiniteInfo.coefficient_eq_sup_KL` in `FiniteKL.lean`; `FiniteInfo.coefficient_binary` in `BinaryKernel.lean` |
| IID finite sources and Boolean functions | `FiniteInfo.iid_binary_bound`, `FiniteInfo.iid_joint_binary_bound` in `Section10.lean` |
| IID observations on any probability space | `iid_joint_random_variable_bound`, `iid_dsbs_random_variable_bound_source` in `Section10RandomVariables.lean` |
| DSBS consequence | `FiniteInfo.iid_dsbs_binary_bound`, `FiniteInfo.iid_dsbs_binary_bound_entropy` |
| Two directed coefficients | `binary_random_variable_bidirectional_bound`, `binary_random_variable_bidirectional_strict` in `RandomVariableDirections.lean` |
| Equal directed constraints | `equal_directed_cap_optimum` in `ReverseChannel.lean` |

Boolean functions use the ordinary type `(Fin n → α) → Bool`. The theorem
`iid_joint_binary_mass` verifies that the constructed output law has exactly
the pushforward masses of the IID product law. The empty sequence `n = 0`
is covered as well.
For existing random variables, `HasIIDJointLaw` specifies the usual joint-atom
product formula. `binaryLaw_iid_joint_eq` proves that their event-based law
agrees with the constructed product-law pushforward. Exact coefficient
tensorization for positive `n` is `FiniteInfo.coefficient_power_succ`.

## Verification

The project uses Lean **4.35.0** and mathlib **4.35.0**, pinned to mathlib
commit `56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`.
All **59 source modules** are imported by the root module and built. `Audit.lean`
contains **121 guarded axiom checks** for the scalar theorem, random-variable interface,
KL interpretation, tensorization, data processing, and Section 10 consequences.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.

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

## Proof map

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
| Joint laws and arbitrary probability spaces | `BinaryLaw`, `BinaryKernel`, `RandomVariables` |
| Finite KL, entropy, and conditional channels | `FiniteEntropy`, `FiniteEntropyConvex`, `FiniteContraction`, `FiniteKL`, `FiniteJoint` |
| Tensorization and Boolean processing | `FiniteTensorization`, `FiniteProcessing`, `Section10` |
| Probability-space IID interface | `FiniteRandomVariables`, `Section10RandomVariables` |
| Both directed coefficients | `ReverseChannel`, `RandomVariableDirections` |

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
  respect to the reference input law (`Supported`). The unchanged input
  contributes the harmless ratio zero. Deterministic sources have coefficient zero.
- Arbitrary finite joint laws are reconstructed from their marginal and
  conditional channel. Choices on null input atoms do not affect the coefficient.
- Section 10's unequal-coefficient assertion is nonattainment of the stated
  upper bound, not a claim to solve the new unequal-constraint optimization problem.
- Contact existence is proved at the actual cap `S(s)` for every nonmerging
  interior source, which is sufficient for the main theorem. A separate
  arbitrary-cap formulation of every assertion in Lemma 4.1 is not claimed.

Source PDF SHA-256:
`dae0f9de685a17492b61838adb0ae72a1a344b518c4456bf55584328614dbe22`.
The PDF and synced project reference files are unchanged.
