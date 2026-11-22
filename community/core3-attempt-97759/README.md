# Core Pillar 3/5 — Truncated Explicit Formula for Dirichlet L-Functions (Playground Attempt #97759)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 3/5 — Truncated Explicit Formula](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-3-5-truncated-e-9cef4156) |
| **Attempt ID** | `#97759` |
| **Playground Score** | `64.14` |
| **Normalized Tokens (`TOKEN_RE`)** | `21,025` vs baseline `129,270` (**83.74% reduction**, `6.15×` smaller) |
| **Characters / Lines / Files** | `80,336` chars vs `423,943` (**81.05% saved**) · `1,575` lines · `1` `.lean` file(s) vs `89` baseline files |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

> [!NOTE]
> Note: After this snapshot (`#97759`, score `64.14`) was selected, `Pi` submitted an even shorter follow-up attempt `#98757` (score `64.77`, `18,762` tokens, `85.49%` token reduction) on the live board, which can replace this commit once author confirmation and licensing are settled.

## Proved Theorem

```lean
theorem AlpogeRHCore3.explicitFormula :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u T : ℝ, 2 ≤ T → T ≤ u →
        ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}).Finite ∧
        ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
          C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
            ∑ᶠ ρ ∈ ZerosBelow χ 1, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖)
```

### Proof Simplification Highlights
Proves critical-strip zero finiteness and the uniform truncated Riemann–von Mangoldt explicit formula for all primitive Dirichlet characters `χ (mod N)` (`C = 10102292`) via Perron kernel bounds (`perronL`), contour shifting (`shiftBound`), and truncation control (`truncChange`) — reducing 89 transitive `.lean` files to 1 file (1,575 lines).

## Corresponding Target Modules in `src/`

- `src/Formalism/PeriodIntegrals/ExplicitFormula.lean` (`PI.ExplicitFormula` / `PI.ExplicitFormulaWith` — verbatim mathematical statement)
- `src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean` (`explicitFormula_closed : PI.ExplicitFormula`)
- `src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ExplicitFormula.lean`

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core3-attempt-97759/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 3/5)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib`, Playground namespace (`AlpogeRHCore3`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Statement matches `PI.ExplicitFormula` in `src/Formalism/PeriodIntegrals/ExplicitFormula.lean` directly.
- Port from standalone `import Mathlib` (Lean `v4.34.1`) to `module` / `public import` / `@[expose] public section` with `autoImplicit = false` under Lean `v4.36.0` (this fork's `main`) or `v4.33.1` (Playground Grand Challenge).
- Check whether downstream modules in `Formalism/PeriodIntegrals/ExplicitFormulaCounts/` also rely on `zerosWindow_closed : PI.ZerosWindow` before pruning transitive files.
