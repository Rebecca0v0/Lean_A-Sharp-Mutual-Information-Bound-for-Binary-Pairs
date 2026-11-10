# BinaryPairBound

Lean formalization of Qianmian Guo, *A Sharp Mutual Information Bound for
Binary Pairs*, arXiv:2611.02392v1 (2 November 2026).

This project starts the verification; it does **not** yet prove Theorem 2.1.
The inequality and its equality classification are recorded as definitions
of propositions in `BinaryPairBound/Specification.lean`. They are not axioms
or theorems with unfinished proofs.

## First milestone

The first proof target is equation (4.1):

```text
Fλ(x) − Tₛ(x) = λ D(x ‖ s) − D(q(x) ‖ q(s)).
```

`Tₛ` uses Lean's actual derivative of `Fλ`. The proof establishes the
derivative by the chain rule, applies the scalar entropy tangent identity,
and simplifies the resulting algebra. The logarithmic-ratio corollary
connects the chosen KL definition to the exact notation in the paper,
including test inputs `x=0` and `x=1`.

**Verified on 10 November 2026:** the complete project builds successfully,
and the axiom audit passes. `equation_4_1` and `equation_4_1_log_ratio` depend
only on `propext`, `Classical.choice`, and `Quot.sound`, the standard
foundations used by mathlib. There are no unfinished proofs or added axioms.
The main theorem remains an unproved specification.

## Files

| File | Purpose |
|---|---|
| `BinaryPairBound/Definitions.lean` | Scalar entropy, KL, channel, mutual information, contraction coefficient, tangent |
| `BinaryPairBound/Specification.lean` | Unproved main inequality and equality targets |
| `BinaryPairBound/Entropy.lean` | Entropy and Bernoulli KL identities |
| `BinaryPairBound/TangentGap.lean` | Chain rule and equation (4.1) |
| `BinaryPairBound.lean` | Root module importing every current proof and specification |
| `Audit.lean` | Axiom inspection for the first milestone |
| `blueprint.md` | Remaining proof obligations and dependencies, matched to the paper |

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
  deterministic input or output. The supremum's bounds and its cap
  characterization remain future proof obligations.
- The theorem specifications include all `s,c,d ∈ [0,1]`, deterministic
  inputs, and both signs of the channel slope. DSBS crossover is not
  restricted to at most `1/2`.
- Theorem 2.1, the probability-theoretic interpretation, and the Section 10
  corollary remain unproved. The blueprint records the work still needed.

Source PDF SHA-256:
`dae0f9de685a17492b61838adb0ae72a1a344b518c4456bf55584328614dbe22`.

The source PDF and synced project reference files are unchanged.
