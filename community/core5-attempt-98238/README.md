# Core Pillar 5/5 — Functorial Resolution of Singularities in Char 0 (Hironaka) (Playground Attempt #98238)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 5/5 — Hironaka Resolution (Char 0)](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-5-5-functorial-d282e185) |
| **Attempt ID** | `#98238` |
| **Playground Score** | `54.37` |
| **Normalized Tokens (`TOKEN_RE`)** | `1,149,791` vs baseline `1,786,589` (**35.64% reduction**, `1.55×` smaller) |
| **Characters / Lines / Files** | `5,067,733` chars vs `8,135,319` (**37.71% saved**) · `116,427` lines · `15` `.lean` file(s) vs `500` baseline files |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Bundle00.lean`, `Bundle01.lean`, `Bundle02.lean`, `Bundle03.lean`, `Bundle04.lean`, `Bundle05.lean`, `Bundle06.lean`, `Bundle07.lean`, `Bundle08.lean`, `Bundle09.lean`, `Bundle10.lean`, `Bundle11.lean`, `Bundle12.lean`, `Bundle13.lean`, `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore5.functorialResolutionCharZero :
    FunctorialResolution.FunctorialResolutionCharZero.{0}
```

### Proof Simplification Highlights
Streamlines the characteristic-zero functorial blow-up resolution stack (`FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero`) into 15 bundled `.lean` modules (`Bundle00.lean`–`Bundle13.lean` + `Solution.lean`, 116,427 lines), cutting over 636k normalized tokens and 3.06M characters compared to the 500-file baseline while remaining 100% `sorry`-free.

## Corresponding Target Modules in `src/`

- `src/Development/ResolutionOfSingularities/Statements.lean` (defines `FunctorialResolution.FunctorialResolutionCharZero`)
- `src/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrongResolution.lean` & `GlobalResolutionFromAffine.lean` (`strongResolutionOfSingularitiesCharZero`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core5-attempt-98238/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 5/5)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib`, Playground namespace (`AlpogeRHCore5`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- `Solution.lean` imports `ComparatorChallenges.RHCore5Defs` (Playground's standalone copy of `src/Development/ResolutionOfSingularities/Statements.lean`) and `Bundle13`.
- To integrate into `src/Development/ResolutionOfSingularities/`: swap `ComparatorChallenges.RHCore5Defs` for `Development.ResolutionOfSingularities.Statements`, convert bundled files to `module` / `public import` / `@[expose] public section` with `autoImplicit = false`, and re-split or namespace modules to match `lakefile.toml` (`Development.+`) without slowing incremental builds.
- Validate across Lean `v4.34.1` → `v4.36.0` (this fork's `main`) / `v4.33.1` (Playground Grand Challenge) on a self-hosted Bohrium runner before replacing any `src/` files.
