# Core Pillar 2/5 — Chebotarev Density Existence Theorem over ℚ (Playground Attempt #98168)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 2/5 — Chebotarev Density (ℚ)](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-2-5-chebotarev-3c22e466) |
| **Attempt ID** | `#98168` |
| **Playground Score** | `61.05` |
| **Normalized Tokens (`TOKEN_RE`)** | `16,440` vs baseline `60,726` (**72.93% reduction**, `3.69×` smaller) |
| **Characters / Lines / Files** | `65,108` chars vs `211,345` (**69.19% saved**) · `1,220` lines · `1` `.lean` file(s) vs `47` baseline files |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore2.chebotarev :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
      ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
        P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P
```

### Proof Simplification Highlights
Establishes existence of unramified primes realizing any prescribed arithmetic Frobenius `σ ∈ Gal(K/ℚ)` outside a finite excluded prime set `T`, via cyclotomic reduction (`cyc_holds`), Dirichlet character orthogonality (`k_holds`), and Lean 4 `grind` automation — collapsing 47 transitive `.lean` files into a single 1,220-line proof.

## Corresponding Target Modules in `src/`

- `src/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean` & `EulerSum.lean` (`namespace ReciprocityTheory.Cheb`, originally `ReciprocityTheory.Cheb.statement_holds`)
- `src/GroundTheory/GlobalFields/TateThesis/Chebotarev.lean` (`GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem`) & `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/ClassFieldRamification/Cheb.lean` (`UpperTheory.V.CF.cheb`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core2-attempt-98168/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 2/5)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib`, Playground namespace (`AlpogeRHCore2`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Replace monolithic `import Mathlib` with fine-grained `public import` headers under `module` / `@[expose] public section`.
- Remove short local abbreviations (`DC`, `Pr`, `sy`, etc.) where helpful for maintainability and add explicit binders for `autoImplicit = false`.
- Note that `UpperTheory.V.CF.cheb` in `src/` is stated for arbitrary base number field `K` (`L/K`), whereas `AlpogeRHCore2.chebotarev` targets the `K/ℚ` existence closure (`ReciprocityTheory.Cheb.statement_holds`); align the wrapper/interface with `ReciprocityTheory.Cheb`.
- Re-verify against Lean `v4.36.0` (this fork's `main`) / `v4.33.1` (Playground Grand Challenge baseline).
