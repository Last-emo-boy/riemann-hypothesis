# Core Pillar 4/5 — Siegel–Walfisz Character Prime Sum Bound (Playground Attempt #98564)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 4/5 — Siegel–Walfisz Bound](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-4-5-siegel-walf-dbc36883) |
| **Attempt ID** | `#98564` |
| **Playground Score** | `64.10` |
| **Normalized Tokens (`TOKEN_RE`)** | `28,451` vs baseline `173,635` (**83.61% reduction**, `6.10×` smaller) |
| **Characters / Lines / Files** | `107,783` chars vs `569,828` (**81.08% saved**) · `1,988` lines · `1` `.lean` file(s) vs `114` baseline files |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore4.siegelWalfisz :
    ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
        2 ≤ x → (q : ℝ) ≤ Real.log x ^ A →
          ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) -
            (if χ = 1 then (x : ℂ) else 0)‖ ≤
            C * x * Real.exp (-c * Real.sqrt (Real.log x))
```

### Proof Simplification Highlights
Establishes the unconditional Dirichlet zero-free region (`zFRDirichlet`, at most one real exceptional zero), Siegel's ineffective lower bound (`exceptional_zero_bound_of`), smoothed character sums (`smoothed_character_sum_of`), and the uniform Siegel–Walfisz prime sum estimate (`siegelWalfisz`) — condensing 114 transitive `.lean` files into 1 file (1,988 lines).

## Corresponding Target Modules in `src/`

- `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean` (`Formalism.ZeroFreeDirichlet.SiegelWalfisz` — verbatim mathematical statement)
- `src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszOf.lean` & `SiegelWalfiszAPOf.lean`

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core4-attempt-98564/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 4/5)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib`, Playground namespace (`AlpogeRHCore4`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Statement matches `Formalism.ZeroFreeDirichlet.SiegelWalfisz` in `src/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean` verbatim.
- Port from standalone `import Mathlib` (Lean `v4.34.1`) to `module` / `public import` / `@[expose] public section` with `autoImplicit = false` under Lean `v4.36.0` (this fork's `main`) or `v4.33.1` (Playground Grand Challenge).
- Check whether downstream callers also import `ZFRDirichlet`, `PsiChiBound`, or `SiegelLower` (all helper ingredients are already proved inside `Solution.lean` and can be re-exported).
