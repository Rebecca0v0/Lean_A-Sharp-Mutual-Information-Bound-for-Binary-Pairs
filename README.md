# BinaryPairBound

Lean formalization of Qianmian Guo, *A Sharp Mutual Information Bound for
Binary Pairs*, arXiv:2611.02392v1 (2 November 2026).

This project starts the verification; it does **not** yet prove Theorem 2.1.
The inequality and its equality classification are recorded as definitions
of propositions in `BinaryPairBound/Specification.lean`. They are not axioms
or theorems with unfinished proofs.

## Verified scope

The current development proves substantial parts of the paper, but the
main theorem is **not complete**. All results listed below have actual Lean
proofs; no unfinished proof or extra axiom stands in for the missing core.

| Part | Checked results / files |
|---|---|
| Section 4.1 | Equation (4.1), actual derivatives, endpoint test inputs; `TangentGap.lean` |
| KL foundations | Positivity, equality, binary data processing; `Divergence.lean` |
| Exact coefficient | `0 ≤ S ≤ 1`, supremum/cap/supporting-tangent equivalences; `Contraction.lean` |
| Information and endpoints | Independence, entropy maximum equality, cap 0/1; `Information.lean`, `Endpoints.lean` |
| Relabeling | Both `J` and `S` invariant under binary label changes; `Symmetry.lean` |
| Section 4.2 | Actual second derivative, exact curvature maximum and distinguished input; `Curvature.lean` |
| Coefficient comparisons | `rhoSquared ≤ S ≤ eta`, equality at the distinguished input; `ChannelCap.lean`, `LocalCoefficient.lean` |
| Lemma 7.1 | Convexity of the posterior-entropy curve; scalar increment bound and equality; `ScalarEntropy.lean` |
| Proposition 7.2 | Finite Bayes identity, Jensen bound, sharp bound and DSBS equality at the distinguished input; `Merging.lean`, `MergingSharp.lean` |
| Symmetric sources | Exact `S(1/2,c,c)=(1-2c)^2`, sharp witnesses for every cap, sufficiency of both equality families; `SymmetricSource.lean` |
| Existence | Closed cap sets, compact optimization, nondegenerate normalized maximizers; `Compactness.lean`, `Optimization.lean` |
| Section 5 calculations | Four actual contact-gap partial derivatives and conditional implicit-slope identities; `DivergenceCalculus.lean`, `Perturbation.lean` |
| Final assembly | `MaximizersMerge → MainTheorem`; `Main.lean` |

The compactness argument proves closedness directly from the fixed-test-input
KL inequalities. It does not assume global continuity of `S` at deterministic
marginals. The local comparison `rhoSquared ≤ S` uses a strict-concavity
contradiction to the supporting tangent, without assuming a quotient limit.

## Remaining core

`Main.lean` defines the **unproved** proposition `MaximizersMerge`: every
normalized maximizer under a cap `0 < lambda < 1` has an interior channel and
its input equals `distinguishedInput`. The checked conditional theorem
`mainTheorem_of_maximizersMerge` shows that this statement suffices for the
unchanged original inequality **and** its full equality classification.
It is not a completed proof of `MainTheorem`.

The remaining work includes the distinct-contact classification, existence
and feasibility of the implicit perturbation family, Proposition 5.1's strict
information derivative signs, boundary improvement, and the cap-saturation
argument. See [the proof blueprint](blueprint.md) for the dependencies.

In particular, `J_le_phi_eta` alone does not prove `J ≤ phi(S)`, and the
implicit-slope identities do not establish an implicit family.

## Verification

The project is checked with Lean 4.35.0 and mathlib 4.35.0. `Audit.lean`
guards the axiom lists for the major milestones: only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. These checks do not remove
explicit hypotheses from conditional theorems. The audit deliberately prints
`MaximizersMerge → MainTheorem` to make the remaining premise visible.

## Build and inspect

Pinned versions: Lean `v4.35.0`, mathlib `v4.35.0` (commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`). Keep `lean-toolchain`,
`lakefile.toml`, and the generated `lake-manifest.json` together.

From this project directory:

```sh
./scripts/check.sh
```

This builds the root module and runs `Audit.lean`. The audit guards its
expected axiom lists: an unexpected assumption causes the check to fail.
The output of the last successful check is saved in `verification.log`.
To run either step alone:

```sh
./scripts/lake.sh build
./scripts/lake.sh env lean Audit.lean
```

The wrapper uses the optional project-local Lean installation in
`.tooling/elan`; otherwise it uses `lake` from your normal installation.
The local compiler and dependency caches are excluded from version control.

On a fresh checkout, install Lean using the official guide at
<https://lean-lang.org/install/>, then download the precompiled library:

```sh
./scripts/lake.sh exe cache get
./scripts/check.sh
```

Open the entire project folder in VS Code with the Lean 4 extension.
For the installation created here, a terminal can use the local tools with:

```sh
export ELAN_HOME="$PWD/.tooling/elan"
export PATH="$ELAN_HOME/bin:$PATH"
```

Launch your editor from that terminal to inherit these settings, or use a
standard Lean installation. No global shell settings are changed by this
project's local setup.

## Mathematical scope

- `H` is mathlib's binary entropy in nats.
- `D x y` is finite Bernoulli KL for `x ∈ [0,1]` and `y ∈ (0,1)`.
  Its total real-valued extension is not extended-real KL at deterministic
  reference distributions.
- `S` is the distribution-dependent supremum from (2.2), with zero for
  deterministic input or output. Its bounds and cap characterization are
  proved in `Contraction.lean`.
- The theorem specifications include all `s,c,d ∈ [0,1]`, deterministic
  inputs, and both signs of the channel slope. DSBS crossover is not
  restricted to at most `1/2`.
- Theorem 2.1, the probability-theoretic interpretation, and the Section 10
  corollary remain unproved. The blueprint records the work still needed.

Source PDF SHA-256:
`dae0f9de685a17492b61838adb0ae72a1a344b518c4456bf55584328614dbe22`.

The source PDF and synced project reference files are unchanged.
