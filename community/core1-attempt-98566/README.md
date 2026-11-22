# Core Pillar 1/5 — Classical Zero-Free Region for ζ(s) (Playground Attempt #98566)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 1/5 — ζ(s) Zero-Free Region](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) |
| **Attempt ID** | `#98566` |
| **Playground Score** | `67.83` |
| **Normalized Tokens (`TOKEN_RE`)** | `1,684` vs baseline `21,641` (**92.22% reduction**, `12.85×` smaller) |
| **Characters / Lines / Files** | `9,303` chars vs `74,010` (**87.43% saved**) · `249` lines · `1` `.lean` file(s) vs `21` baseline files |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

> [!NOTE]
> Note: After this snapshot (`#98566`, score `67.83`) was selected, `Pi` submitted an even shorter follow-up attempt `#98740` (score `68.07`, `1,596` tokens, `92.63%` token reduction) on the live board, which can replace this commit once author confirmation and licensing are settled.

## Proved Theorem

```lean
theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0
```

### Proof Simplification Highlights
Replaces custom Cauchy/Euler–Maclaurin contour machinery with Mathlib's `BorelCaratheodory` theorem, divided-difference zero peeling (`dslope` / `sub_smul_dslope_of_zero`), Möbius inversion `1/ζ` bounds, and Lean 4 `grind` automation — compressing 21 transitive `.lean` files into a single 249-line proof.

## Corresponding Target Modules in `src/`

- `src/Formalism/ZetaNonvanishing/ZetaLandau.lean` & `Assembly.lean` / `MellinSgen.lean` / `GzLipschitz.lean`
- `src/Formalism/LandauZeroFreeBounds/Statement.lean` (`Formalism.ZeroFreeDirichlet.ZFRDirichlet` specialized at `q = 1, χ = 1`; originally `Formalism.ZF.zeroFreeRegion` in Alpöge's pre-reorganization tree)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core1-attempt-98566/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 1/5)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib`, Playground namespace (`AlpogeRHCore1`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Replace monolithic `import Mathlib` with targeted `public import` statements and Lean 4.36 `module` / `@[expose] public section` headers.
- Make implicit binders explicit to satisfy `autoImplicit = false` / `relaxedAutoImplicit = false` in `lakefile.toml`.
- Verify `grind` and `ZetaAsymptotics` / `BorelCaratheodory` API compatibility across Lean `v4.34.1` → `v4.33.1` (Playground baseline) / `v4.36.0` (this fork's `main`).
- Bridge `AlpogeRHCore1.zeroFreeRegion` to the downstream consumers in `src/Formalism/ZetaNonvanishing/` and `src/Formalism/LandauZeroFreeBounds/`.
