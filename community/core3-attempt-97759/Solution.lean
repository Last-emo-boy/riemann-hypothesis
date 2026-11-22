import Mathlib

noncomputable section

namespace EF

open Complex hiding log exp log_zero log_inv norm_natCast exp_nat_mul cosh log_mul
open Real hiding Gamma Gamma_one sin_add_pi_div_two norm_natCast exp
open Finset hiding uIcc Icc uIcc_of_le
open Set hiding mem_Icc disjoint_left mem_range
open MeasureTheory hiding integral_smul integral_const_mul integral_div norm_integral_le_of_norm_le_const integral_neg
open Filter hiding mem_sdiff
open Topology Metric DirichletCharacter intervalIntegral Or LSeries Asymptotics IsBigO
open ArithmeticFunction hiding log
open Nat (cast_analyticOrderNatAt lt_floor_add_one succ_pos one_le_iff_ne_zero floor_le cast_sub cast_pos cast_nonneg one_le_cast strong_induction_on exists_eq_succ_of_ne_zero add_sub_of_le cast_eq_zero cast_add_one cast_ofNat cast_sum lt_succ_iff cast_zero cast_add cast_one floor_pos cast_lt cast_le lt_of_floor_lt floor measurable_floor)
open Int (fract abs_fract fract_lt_one natCast_floor_eq_floor natCast_ne_zero one_le_abs)
open Iff (mp mpr)
open Eventually (of_forall mono)
open Set.Finite (toFinset mem_toFinset toFinset_mono toFinset_subset)
open MeromorphicOn (divisor)
open LE.le (trans_eq)
open Inv (inv)
open Function (mem_support)
open NeZero (pos ne)
open Classical
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

abbrev cl := Complex.log
abbrev cext := @Complex.ext
abbrev τ : ℂ := 2 * π
abbrev τI : ℂ := τ * I
abbrev rN (n : ℕ) : ℝ := n
abbrev cR (x : ℝ) : ℂ := x
abbrev cpx (x y : ℝ) : ℂ := ↑x + ↑y * I
abbrev aim (z : ℂ) := abs (im z)
abbrev LN (N : ℕ) (t : ℝ) : ℝ := log (N * (abs t + 2))
abbrev ldL := logDeriv (LFunction χ)
lemma one_le_N (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := mpr one_le_cast (pos N)
lemma half_le_log {x} (h : 2 ≤ x := by nlinarith) : 0.69 ≤ log x := by linarith [log_le_log two_pos h, log_two_gt_d9]
lemma half_le_LN (N : ℕ) [NeZero N] t : 0.69 ≤ LN N t := half_le_log (by nlinarith [one_le_N N, abs_nonneg t])
lemma log_le_2log {x y} (h : x ≤ y ^ 2) (hx : 0 < x := by positivity) : log x ≤ 2 * log y := by
  simpa using trans_eq (log_le_log hx h) (log_pow y 2)
lemma arsinh_le_log {x} (hx : 0 ≤ x := by linarith) : arsinh x ≤ log (1 + 2 * x) :=
  log_le_log (by positivity) (by linarith [mpr sqrt_le_iff ⟨by linarith, (by nlinarith : 1 + x ^ 2 ≤ (1 + x) ^ 2)⟩])
lemma nneg {a : ℂ} {B} (h : norm a ≤ B) : norm (-a) ≤ B := by simpa using h
lemma nadd2 {a b c : ℂ} {B C} (hb : norm b ≤ B) (hc : norm c ≤ C) (h : a = b + c := by ring1) : norm a ≤ B + C :=
  h ▸ le_trans (norm_add_le b c) (add_le_add hb hc)
lemma nadd3 {a b c d : ℂ} {B C D} (hb : norm b ≤ B) (hc : norm c ≤ C) (hd : norm d ≤ D) (h : a = b + c + d := by ring1) :
    norm a ≤ B + C + D :=
  h ▸ le_trans norm_add₃_le (add_le_add (add_le_add hb hc) hd)

def ZerosBelow T :=
  {ρ | 0 < re ρ ∧ re ρ < 1 ∧ |im ρ| < T ∧ LFunction χ ρ = 0}

def ZerosNear t :=
  {ρ | 0 < re ρ ∧ re ρ < 1 ∧ |im ρ - t| ≤ 1 ∧ LFunction χ ρ = 0}

abbrev mult ρ := analyticOrderNatAt (LFunction χ) ρ
abbrev mC (ρ : ℂ) : ℂ := mult χ ρ
abbrev mR ρ := rN (mult χ ρ)

def eps0 : ℂ := if χ.Even ∧ χ ≠ 1 then 1 else 0
def del1 : ℂ := if χ = 1 then 1 else 0

def psiRaw (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)

def zsum T (u : ℝ) := ∑ᶠ ρ ∈ ZerosBelow χ T, mC χ ρ * (↑u ^ ρ / ρ)
def S1 := ∑ᶠ ρ ∈ ZerosBelow χ 1, mR χ ρ / norm ρ

def GoodHeight T' :=
  ∀ ρ, 0 < re ρ → re ρ < 1 → LFunction χ ρ = 0 →
    inv (1600 * log (N * T')) ≤ |(|im ρ|) - T'|

def cLine u := 1 + inv (log u)

lemma rpow_cLine {u} (hu : 2 ≤ u) : u ^ cLine u = rexp 1 * u := by
  rw [cLine, rpow_add <| by linarith, rpow_one, rpow_def_of_pos <| by linarith, mul_inv_cancel₀ (log_pos <| by linarith).ne', mul_comm]

def Err (N : ℕ) u T := u * log (N * u * T) ^ 2 / T + log (N * u)

def rectInt (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :=
  (∫ x in x0..x1, f (cpx x y0)) - (∫ x in x0..x1, f (cpx x y1)) +
    I • (∫ y in y0..y1, f (cpx x1 y)) - I • ∫ y in y0..y1, f (cpx x0 y)

def rect (x0 x1 y0 y1 : ℝ) := Icc x0 x1 ×ℂ Icc y0 y1

def perronK (y : ℝ) c T :=
  inv τ * ∫ t in (-T)..T, ↑y ^ cpx c t / cpx c t

def kb T y := if log y = 0 then 1 + arsinh T else min (1 + arsinh T) (inv (T * abs (log y)))

lemma norm_int_inv_sqrt {f : ℝ → ℂ} {T : ℝ} {C} (hT : 0 ≤ T) (h : ∀ t ∈ Ioc (-T) T, ‖f t‖ ≤ C * inv √(1 + t ^ 2)) :
    ‖∫ t in -T..T, f t‖ ≤ 2 * C * arsinh T := by
  have hci : IntervalIntegrable (fun t => inv √(1 + t ^ 2)) volume (-T) T :=
    Continuous.intervalIntegrable (by fun_prop (disch := intro _
                                                         positivity)) _ _
  grw [norm_integral_le_of_norm_le (by linarith) (of_forall h) (hci.const_mul C)]
  rw [integral_const_mul, integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_arsinh t) hci, arsinh_neg]
  linarith

def vertInt u T' :=
  inv τ * ∫ t in (-T')..T',
    (-ldL χ (cpx (cLine u) t)) * (↑u ^ cpx (cLine u) t / cpx (cLine u) t)

variable {χ : DirichletCharacter ℂ N}
lemma ne_one_of_ne_one (h : χ ≠ 1) : N ≠ 1 := fun hN => h (by subst hN
                                                              exact level_one χ)
lemma norm_eps0 : ‖eps0 χ‖ ≤ 1 := by
  unfold eps0
  split_ifs <;> simp
lemma norm_del1 : ‖del1 χ‖ ≤ 1 := by
  unfold del1
  split_ifs <;> simp
section InputsSec
open scoped ArithmeticFunction.Moebius

lemma logDeriv_prod_factor {f h : ℂ → ℂ} {Z} {m : ℂ → ℕ} {s}
    (hfac : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hne : ∀ ρ ∈ Z, s - ρ ≠ 0) (hh0 : h s ≠ 0) (hhd : DifferentiableAt ℂ h s) :
    logDeriv f s = logDeriv h s + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) := by
  have hp0 ρ (h : ρ ∈ Z) := pow_ne_zero (m ρ) (hne ρ h)
  rw [(logDeriv_congr_nhds hfac).eq_of_nhds]
  change logDeriv ((fun z => ∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h) s = _
  rw [logDeriv_mul s (mpr prod_ne_zero_iff hp0) hh0 (by fun_prop) hhd,
    ← prod_fn, logDeriv_prod hp0 fun _ _ => by fun_prop,
    sum_congr rfl fun _ _ => by rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply, deriv_sub_const, deriv_id'', mul_one_div], add_comm]

open ZetaAsymptotics in
lemma tsum_rpow_le {s : ℝ} (hs : 1 < s) : ∑' n, (rN n + 1) ^ (-s) ≤ 1 + inv (s - 1) := by
  have := zeta_limit_aux1 hs
  simp_rw [rpow_neg (by positivity : 0 ≤ rN _ + 1), inv_eq_one_div]
  nlinarith [show 0 ≤ termTSum s from tsum_nonneg fun _ => term_nonneg _ _]

lemma mellin_strip {f : ℂ → ℂ} {g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hf : Differentiable ℂ f)
    (hgm : Measurable g) (hgb : ∀ x, ‖g x‖ ≤ C)
    (heq : ∀ {z}, 1 < re z → f z = z * ∫ x in Ioi (1 : ℝ), g x * (x : ℂ) ^ (-z - 1))
    {s} (hs : 0.5 ≤ re s) : ‖f s‖ ≤ 2 * C * norm s := by
  let F := indicator (Ioi 1) g
  have hFb x : ‖F x‖ ≤ C := le_trans (norm_indicator_le_norm_self _ _) (hgb x)
  have hme z : mellin F (-z) = ∫ x in Ioi (1 : ℝ), g x * (x : ℂ) ^ (-z - 1) := by
    rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi]
    simpa [Ioi_inter_Ioi] using setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp [mul_comm]
  have hfs : f s = s * mellin F (-s) := (hf.differentiableOn.analyticOnNhd (isOpen_re_gt 0)).eqOn_of_preconnected_of_eventuallyEq
    ((DifferentiableOn.analyticOnNhd (f := fun z => z * mellin F (-z)) fun z hz => by
      have := mellin_differentiableAt_of_isBigO_rpow (f := F) (s := -z) (a := 0)
        ((locallyIntegrableOn_const C).mono (hgm.indicator measurableSet_Ioi).aestronglyMeasurable (of_forall fun x => by simpa [norm_of_nonneg hC] using hFb x))
        (of_bound C (of_forall fun x => by simpa using hFb x)) (by simpa)
        (of_bound' (by
          filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
          simp [F, hx.2.not_gt])) (sub_one_lt _)
      fun_prop) (isOpen_re_gt 0))
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num)
    (mono ((isOpen_re_gt 1).mem_nhds (by norm_num)) fun z hz => by simp [heq hz, hme]) (show 0 < re s by linarith)
  rw [hfs, hme, norm_mul]
  grw [MeasureTheory.norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by linarith : -re s - 1 < -1) zero_lt_one).const_mul C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      grw [norm_mul, hgb x, norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx)]
      simp),
    MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  simp
  grw [inv_anti₀ (by norm_num) hs]
  norm_num
  linarith

lemma chk_zeta0Bound {s} (hs : 0.5 ≤ re s) : ‖riemannZeta₀ s‖ ≤ 1 + 2 * norm s := by
  have hfb (x : ℝ) : ‖cR (fract x)‖ ≤ 1 := by
    simp
    grind [abs_fract, fract_lt_one]
  have h0 := mellin_strip zero_le_one
    ((differentiable_const 1).sub differentiable_riemannZeta₀) (by fun_prop) hfb (fun {z} hz => by
      have h := LSeries_one_eq_riemannZeta hz ▸ LSeries_eq_mul_integral' 1 zero_le_one hz (by
        simp
        rfl)
      simp at h
      rw [(setIntegral_congr_fun measurableSet_Ioi fun x hx => by
            have hx0 := lt_trans zero_lt_one hx.out
            have := mpr ofReal_ne_zero hx0.ne'
            simp [fract, ← natCast_floor_eq_floor hx0.le, cpow_add _ _ this, cpow_neg_one, add_comm, sub_eq_add_neg]
            field).trans (integral_sub (integrableOn_Ioi_cpow_of_lt (a := -z) (by simpa) zero_lt_one)
          ((integrableOn_Ioi_cpow_of_lt (a := -z - 1) (by
            simp
            linarith) zero_lt_one).mul_bdd (by fun_prop) (of_forall hfb))),
        integral_Ioi_cpow_of_lt (by simpa) zero_lt_one] at h
      simp [riemannZeta₀, (by grind [one_re] : z ≠ 1)] at h ⊢
      grind [one_re]) hs
  simp at h0
  exact nadd2 norm_one.le (nneg h0)

lemma chk_lBoundRight (hpx : χ ≠ 1) {s} (hs : 0.5 ≤ re s) (h2 : re s ≤ 8) :
    ‖LFunction χ s‖ ≤ 20 * (N * (aim s + 2)) := by
  let Ap n := ∑ k ∈ range n, χ k
  have hzero : ∑ n ∈ range N, χ n = 0 := by
    obtain ⟨m, rfl⟩ := exists_eq_succ_of_ne_zero (ne N)
    rw [← Fin.sum_univ_eq_sum_range, ← MulChar.sum_eq_zero_of_ne_one hpx]
    exact sum_congr rfl fun (i : ZMod (m + 1)) _ => congrArg χ (ZMod.natCast_zmod_val i)
  have hB K : ‖Ap K‖ ≤ N := by
    induction K using strong_induction_on with | _ K ih =>
      by_cases hK : K < N
      · grw [norm_sum_le, sum_le_sum fun _ _ => norm_le_one χ _]
        simpa using hK.le
      · rw [show Ap K = Ap (K - N) by
          rw [← add_sub_of_le (mp not_lt hK)]
          simp [Ap, sum_range_add, hzero]]
        exact ih _ (by have := pos N
                       omega)
  have := mellin_strip (g := (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ k) ∘ floor) (cast_nonneg N)
    (differentiable_LFunction hpx) (measurable_from_top.comp measurable_floor)
    (fun x => by
      convert hB (⌊x⌋₊ + 1) using 2
      simp [Ap, sum_range_eq_add_Ico _ (succ_pos _), χ.map_zero' (ne_one_of_ne_one hpx)]
      rfl)
    (fun {z} hz => by
      rw [LFunction_eq_LSeries χ hz, LSeries_eq_mul_integral' (fun n => χ n) zero_le_one hz (isBigO_of_le _ fun n => by
        grw [norm_of_nonneg (by positivity), sum_le_sum fun _ _ => norm_le_one χ _]
        simp)]
      simp [sub_eq_add_neg, add_comm]) hs
  nlinarith [norm_le_abs_re_add_abs_im s, abs_of_pos (by linarith : 0 < re s), abs_nonneg (im s), one_le_N N]
end InputsSec

def Lent (χ : DirichletCharacter ℂ N) : ℂ → ℂ := if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

lemma differentiable_Lent (χ : DirichletCharacter ℂ N) : Differentiable ℂ (Lent χ) := by
  unfold Lent
  split_ifs with h
  exacts [differentiable_LFunctionTrivChar₁ N, differentiable_LFunction h]

lemma analytic_Lent (χ : DirichletCharacter ℂ N) {U} : AnalyticOnNhd ℂ (Lent χ) U :=
  fun z _ => (differentiable_Lent χ).analyticAt z

lemma Lent_one_apply (h : χ = 1) {s} (hs : s ≠ 1) :
    Lent χ s = (s - 1) * LFunction χ s := by
      subst h
      simp [Lent, hs]

lemma Lent_one_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 1 ≠ 0 := by
  unfold Lent
  split_ifs with h
  exacts [LFunctionTrivChar₁_apply_one_ne_zero N, LFunction_apply_one_ne_zero h]

lemma Lent_eq_zero_iff {s} (hs : s ≠ 1) : Lent χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  · simp [Lent_one_apply h hs, sub_eq_zero, hs]
  · simp [Lent, h]

lemma Lent_ev (h : χ = 1) {s} (hs : s ≠ 1) :
    Lent χ =ᶠ[𝓝 s] (fun z => z - 1) * LFunction χ :=
  mono (isOpen_ne.mem_nhds hs) fun _ => Lent_one_apply h

lemma order_Lent {s} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  · have hL := DifferentiableOn.analyticAt (fun z hz => (differentiableAt_LFunction χ z (inl hz)).differentiableWithinAt) (isOpen_ne.mem_nhds hs)
    have h1 : AnalyticAt ℂ (fun z => z - 1) s := by fun_prop
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr (Lent_ev h hs), analyticOrderAt_mul h1 hL, mpr h1.analyticOrderAt_eq_zero (sub_ne_zero_of_ne hs), zero_add]
  · simp [Lent, h]

lemma Lent_order_ne_top (χ : DirichletCharacter ℂ N) (ρ) : analyticOrderAt (Lent χ) ρ ≠ ⊤ := fun h =>
  Lent_one_ne_zero χ ((analytic_Lent χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ ρ) (mp analyticOrderAt_eq_top h) (mem_univ 1))

lemma logDeriv_Lent {s} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    ldL χ s = logDeriv (Lent χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  · rw [(logDeriv_congr_nhds (Lent_ev h hs)).eq_of_nhds,
      logDeriv_mul (f := (· - 1)) s (sub_ne_zero_of_ne hs) h0 (by fun_prop)
        (differentiableAt_LFunction χ s (inl hs)), show logDeriv (· - 1) s = inv (s - 1) by simp [logDeriv_apply]]
    simp only [del1, ite_eq_left h]
    ring
  · simp [Lent, del1, h]

lemma div_Lent {U u} (hu : u ∈ U) :
    divisor (Lent χ) U u = analyticOrderNatAt (Lent χ) u := by
  rw [MeromorphicOn.divisor_apply (analytic_Lent χ).meromorphicOn hu, (analytic_Lent χ u hu).meromorphicOrderAt_eq, ← cast_analyticOrderNatAt (Lent_order_ne_top χ u)]
  simp

lemma div_Lent_ne_zero {U u} (hu : u ∈ U) : divisor (Lent χ) U u ≠ 0 ↔ Lent χ u = 0 := by
  rw [div_Lent hu, natCast_ne_zero, ne_eq, ← cast_eq_zero (R := ℕ∞), cast_analyticOrderNatAt (Lent_order_ne_top χ u),
    ((differentiable_Lent χ).analyticAt u).analyticOrderAt_eq_zero, not_not]

lemma extract_zeros_Lent (χ : DirichletCharacter ℂ N) {U} (hUc : IsCompact U) (hUp : IsPreconnected U) (hUn : U.Nontrivial) :
    ∃ Z : Finset ℂ, ∃ g, (∀ ρ, ρ ∈ Z ↔ ρ ∈ U ∧ Lent χ ρ = 0) ∧
      AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧
      ∀ z ∈ U, Lent χ =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ mult χ ρ) * g w := by
  have hf := analytic_Lent χ (U := U)
  let D := divisor (Lent χ) U
  have hDfin := D.finiteSupport hUc
  have hmem ρ : ρ ∈ toFinset hDfin ↔ ρ ∈ U ∧ Lent χ ρ = 0 := by
    by_cases h : ρ ∈ U <;> simp [h, D, div_Lent_ne_zero, mem_toFinset hDfin]
  obtain ⟨g, hg, hg0, heq⟩ := hf.meromorphicOn.extract_zeros_poles (fun ⟨u, hu⟩ => by
    simp [(hf u hu).meromorphicOrderAt_eq, Lent_order_ne_top χ u]) hDfin
  refine ⟨toFinset hDfin, g, hmem, hg, fun z hz => hg0 ⟨z, hz⟩, fun z hz => ?_⟩
  let rhs w := (∏ ρ ∈ toFinset hDfin, (w - ρ) ^ mult χ ρ) * g w
  have hrhs : AnalyticAt ℂ rhs z := (analyticAt_fun_prod _ fun _ _ => by fun_prop).mul (hg z hz)
  exact mp ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hrhs.continuousAt)
    ((hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect hrhs.meromorphicAt hz (hUp.preperfect_of_nontrivial hUn)
      (heq.trans (of_forall fun w => by
        rw [Pi.smul_apply', finprod_eq_prod_of_mulSupport_subset _ (by simp [Function.FactorizedRational.mulSupport] : (fun u => (· - u) ^ D u).mulSupport ⊆ hDfin.toFinset),
          prod_apply, smul_eq_mul]
        exact congrArg (· * g w) (prod_congr rfl fun ρ hrx => by
          obtain ⟨hU, h0⟩ := mp (hmem ρ) hrx
          simp [D, div_Lent hU, order_Lent fun e => Lent_one_ne_zero χ (e ▸ h0)]))))

lemma zerosFinite (χ : DirichletCharacter ℂ N) (T) : (ZerosBelow χ T).Finite :=
  ((divisor (Lent χ) (rect 0 1 (-T) T)).finiteSupport (isCompact_Icc.reProdIm isCompact_Icc)).subset fun ρ ⟨h0, h1, him, hL⟩ =>
    mpr mem_support (mpr (div_Lent_ne_zero ⟨⟨h0.le, h1.le⟩, mp abs_le him.le⟩) (mpr (Lent_eq_zero_iff (by grind [one_re])) hL))

lemma mem_window {ρ t}
    (h0 : 0 < re ρ) (h1 : re ρ < 1) (hL : LFunction χ ρ = 0) (h : |(|im ρ|) - t| ≤ 1) :
    ρ ∈ ZerosNear χ t ∪ ZerosNear χ (-t) := by
  by_cases hi : 0 ≤ im ρ <;> [left; right] <;> exact ⟨h0, h1, by grind, hL⟩

section PrimSec
variable (hpx : IsPrimitive χ)
include hpx

lemma completed_ne_zero_left {s}
    (hs : re s ≤ 0) (h1 : χ ≠ 1 ∨ s ≠ 0) : completedLFunction χ s ≠ 0 := fun h0 => by
  have hp := (show IsPrimitive χ⁻¹ by rwa [IsPrimitive, conductor_inv]).completedLFunction_one_sub s
  simp [h0] at hp
  have h2 := LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (inl (by grind [one_re, sub_re]))
  rw [hp, zero_div] at h2
  exact LFunction_ne_zero_of_one_le_re χ⁻¹ (h1.imp (mpr inv_ne_one) (by grind)) (by
    simp
    linarith) h2

lemma zeroLocus {s}
    (hs : -1.5 ≤ re s) (hs1 : s ≠ 1) (hL : LFunction χ s = 0) :
    (0 < re s ∧ re s < 1) ∨ (s = 0 ∧ χ.Even ∧ χ ≠ 1) ∨ (s = -1 ∧ χ.Odd) := by
  by_cases hre1 : 1 ≤ re s
  · exact absurd hL (LFunction_ne_zero_of_one_le_re χ (inr hs1) hre1)
  by_cases hre0 : 0 < re s
  · exact inl ⟨hre0, by linarith⟩
  right
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by
    by_contra h
    obtain ⟨rfl, rfl⟩ : χ = 1 ∧ s = 0 := by grind
    obtain rfl : N = 1 := by simpa [IsPrimitive, conductor_one] using hpx.symm
    norm_num [LFunction_modOne_eq, riemannZeta_zero] at hL
  have hdiv := LFunction_eq_completed_div_gammaFactor χ s (hc'.elim (inr ∘ ne_one_of_ne_one) inl)
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  have := hdiv.resolve_left (completed_ne_zero_left hpx (by linarith) hc')
  have hgn {w} (hw : -1.5 ≤ re w) (h : Gammaℝ w = 0) : w = 0 := by
    obtain ⟨_ | n, rfl⟩ := mp Gammaℝ_eq_zero_iff h
    · simp
    · simp at hw
      linarith
  rcases even_or_odd χ with he | ho
  · have h0 := hgn hs (by rwa [← he.gammaFactor_def])
    exact inl ⟨h0, he, by grind⟩
  · have h0 := hgn (w := s + 1) (by simp
                                    linarith) (by rwa [← ho.gammaFactor_def])
    exact inr ⟨by grind, ho⟩

theorem mult_zero_of_even (he : χ.Even)
    (h1 : χ ≠ 1) : LFunction χ 0 = 0 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  let g (s : ℂ) := ↑π ^ (s / 2) * (inv 2 * inv (Gamma (s / 2 + 1)))
  have hLeq s : LFunction χ s = completedLFunction χ s * (s * g s) := by
    rw [LFunction_eq_completed_div_gammaFactor χ s (inr (ne_one_of_ne_one h1)), he.gammaFactor_def, div_eq_mul_inv,
      Gammaℝ_def, neg_div, cpow_neg, mul_inv, inv_inv]
    by_cases hs : s = 0
    · simp [hs]
    simp only [g, Gamma_add_one _ (div_ne_zero hs two_ne_zero), mul_inv]
    field_simp
  refine ⟨by simp [hLeq], ?_⟩
  rw [analyticOrderNatAt, mpr (((differentiable_LFunction h1).analyticAt 0).analyticOrderAt_eq_natCast (n := 1))
    ⟨fun s => completedLFunction χ s * g s, ((differentiable_completedLFunction h1).mul
      (((differentiable_id.div_const 2).const_cpow (inl (by exact_mod_cast pi_ne_zero))).mul
        ((differentiable_one_div_Gamma.comp (by fun_prop)).const_mul _))).analyticAt 0,
      mul_ne_zero (completed_ne_zero_left hpx (by simp) (inl h1)) (by simp [g, Gamma_one]),
      of_forall fun z => by
        simp [hLeq]
        ring⟩]
  rfl

lemma zeroStrip {s} (hs : -0.5 ≤ re s := by linarith) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hL : LFunction χ s = 0) :
    0 < re s ∧ re s < 1 := by
  rcases zeroLocus hpx (by linarith) hs1 hL with h | ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [h, absurd rfl hs0, by norm_num at hs]

lemma L0_iff : LFunction χ 0 = 0 ↔ χ.Even ∧ χ ≠ 1 :=
  ⟨fun h => by rcases zeroLocus hpx (by norm_num) zero_ne_one h with ⟨a, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> simp_all,
   fun ⟨he, h1⟩ => (mult_zero_of_even hpx he h1).1⟩

open scoped ZMod in
lemma norm_L_one_sub_le {w}
    (h1 : 0.5 ≤ re w) (h2 : re w ≤ 5) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 12 * rN N ^ 5 * (aim w + 7) ^ 7 * ‖LFunction χ⁻¹ w‖ := by
  have hGd : ‖Gamma w‖ * rexp (π / 2 * aim w) ≤ 6 * (aim w + 7) ^ 7 := by
    let z := cpx 0.5 (im w)
    let b : ℝ := 7.5 - re w
    have hb : 2 ≤ b := by grind
    have hB := congrArg norm (Gamma_mul_Gamma_eq_betaIntegral (s := w) (t := b) (by linarith) (by
      simp
      linarith))
    rw [norm_mul, norm_mul, show w + b = z + 7 from cext (by simp [z, b]
                                                             ring) (by simp [z]),
      Gamma_ofReal, norm_real, norm_of_nonneg (le_of_lt (Gamma_pos_of_pos (by linarith)))] at hB
    have : ‖betaIntegral w b‖ ≤ 2 := by
      refine trans_eq (norm_integral_le_of_norm_le zero_le_one (of_forall fun x ⟨hx0, hx1⟩ => ?_)
        (intervalIntegrable_rpow' (r := -0.5) (by norm_num))) (by
          rw [integral_rpow (inl (by norm_num))]
          norm_num)
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, ← ofReal_one, ← ofReal_sub,
        norm_cpow_eq_rpow_re_of_nonneg (by linarith) (by simp
                                                         linarith)]
      grw [rpow_le_one (x := 1 - x) (by linarith) (by linarith) (by simp
                                                                    linarith), mul_one]
      exact rpow_le_rpow_of_exponent_ge hx0 hx1 (by simp
                                                    linarith)
    have hG7z (k : ℕ) (hk : k ≤ 7) : ‖Gamma (z + k)‖ ≤ (aim w + 7) ^ k * ‖Gamma z‖ := by
      induction k with
      | zero => simp
      | succ m ih =>
        rw [cast_add_one, ← add_assoc, Gamma_add_one _ (ne_of_apply_ne re (by simp [z]
                                                                              linarith)), norm_mul, pow_succ', mul_assoc]
        grw [show ‖z + m‖ ≤ aim w + 7 by
            have := norm_le_abs_re_add_abs_im (z + m)
            simp [z] at this
            have : rN m ≤ 6 := by norm_cast
                                  omega
            grind [cast_nonneg m],
          ih (by omega)]
    have half_line : ‖Gamma z‖ * rexp (π / 2 * aim w) ≤ 3 := by
      have h := Gamma_mul_Gamma_one_sub z
      rw [show 1 - z = (starRingEnd ℂ) z by apply cext <;> simp [z]
                                            norm_num, Gamma_conj, mul_conj,
        show (π : ℂ) * z = ↑(π * im w) * I + π / 2 by
          apply cext <;> simp [z]
          ring,
        sin_add_pi_div_two, cos_mul_I, ← ofReal_cosh] at h
      have hsqG : ‖Gamma z‖ ^ 2 = π / cosh (π * im w) := by exact_mod_cast normSq_eq_norm_sq _ ▸ h
      let y := π * aim w
      have : rexp y / 2 ≤ cosh (π * im w) := by
        rw [← cosh_abs, abs_mul, abs_of_pos pi_pos, cosh_eq]
        linarith [exp_pos (-y)]
      have : (‖Gamma z‖ * rexp (π / 2 * aim w)) ^ 2 ≤ 9 := by
        rw [mul_pow, hsqG, ← exp_nat_mul, cast_ofNat, ← mul_assoc, mul_div_cancel₀ _ two_ne_zero,
          div_mul_eq_mul_div, div_le_iff₀ (cosh_pos _)]
        nlinarith [pi_lt_four, exp_pos y]
      nlinarith
    have hGb := Gamma_strictMonoOn_Ici.monotoneOn (a := 2) (by simp) hb hb
    simp at hGb
    have h7 := hG7z 7 le_rfl
    norm_num at h7
    grw [show ‖Gamma w‖ ≤ 2 * ‖Gamma (z + 7)‖ by nlinarith [norm_nonneg (Gamma w), norm_nonneg (Gamma (z + 7))], h7]
    nlinarith [half_line, (by positivity : 0 ≤ (aim w + 7) ^ 7)]
  let cf : ZMod N → ℂ := χ
  set L := ‖LFunction χ⁻¹ w‖
  let zL := @ZMod.LFunction N _
  rw [LFunction, ZMod.LFunction_one_sub _ (fun n hn => by simp [hn] at h1
                                                          linarith) h]
  have hsmul c f : zL (c • f) w = c * zL f w := by simp [zL, ZMod.LFunction, mul_sum, mul_assoc, mul_left_comm]
  have hA : ‖zL (𝓕 cf) w‖ ≤ N * L := by
    rw [show 𝓕 cf = (gaussSum χ ZMod.stdAddChar * χ⁻¹ (-1)) • (χ⁻¹ : DirichletCharacter ℂ N) from funext fun k => by
      rw [hpx.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]
      simp
      ring, hsmul, norm_mul, norm_mul]
    unfold gaussSum
    grw [norm_sum_le, sum_le_sum (g := fun _ => 1) fun a _ => by
      simpa [ZMod.stdAddChar_apply] using norm_le_one χ a, norm_le_one χ⁻¹ (-1)]
    simp [L, zL, LFunction]
  have hB : ‖zL (𝓕 fun x => cf (-x)) w‖ ≤ N * L := by
    rw [show (fun x => cf (-x)) = χ (-1) • cf from funext fun x => by simp [cf, ← map_mul], map_smul, hsmul, norm_mul]
    grw [norm_le_one χ (-1), hA, one_mul]
  have he {a} (ha : re a ≤ π / 2 * aim w) := (norm_exp a).symm ▸ mpr exp_le_exp ha
  simp only [norm_mul]
  rw [norm_natCast_cpow_of_pos (pos N), ← ofReal_ofNat, ← ofReal_mul, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  grw [rpow_le_rpow_of_exponent_le (one_le_N N) (by simp
                                                    linarith : re (w - 1) ≤ (4 : ℕ)), rpow_natCast,
    rpow_le_one_of_one_le_of_nonpos (by linarith [pi_gt_three]) (by simp
                                                                    linarith),
    norm_add_le, norm_mul, norm_mul,
    he (by simp
           nlinarith [neg_le_abs (im w), pi_pos]), he (by simp
                                                          nlinarith [le_abs_self (im w), pi_pos]), hA, hB]
  nlinarith [hGd, show 0 ≤ rN N ^ 5 * L by positivity]

lemma lGrowth {s} (h1 : -4 ≤ re s) (h2 : re s ≤ 8) :
    ‖Lent χ s‖ ≤ 2 ^ 35 * (N * (aim s + 2)) ^ 10 := by
  set Y := aim s + 2
  have hY : 2 ≤ Y := by linarith [abs_nonneg (im s)]
  by_cases hc : χ = 1
  · subst hc
    obtain rfl : N = 1 := by simpa [IsPrimitive, conductor_one] using hpx.symm
    simp
    rw [show Lent 1 s = riemannZeta₁ s by
      by_cases hz : s = 1
      · simp [Lent, hz]
      · simp [Lent, LFunctionTrivChar₁, LFunction_modOne_eq]
        grind [riemannZeta_eq_inv_sub_mul]]
    have hzR {z} (a : 0.5 ≤ re z) (b : re z ≤ 8) : ‖riemannZeta₁ z‖ ≤ 150 * (aim z + 2) ^ 2 := by
      rw [riemannZeta₁]
      grw [norm_add_le, norm_mul, norm_sub_le, norm_one, chk_zeta0Bound a]
      nlinarith [norm_le_abs_re_add_abs_im z, abs_of_pos (by linarith : 0 < re z), abs_nonneg (im z), norm_nonneg z]
    have hzL {z} (a : -4 ≤ re z) (b : re z < 0.5) (c : 0.5 ≤ norm z) : ‖riemannZeta₁ z‖ ≤ 2 ^ 31 * (aim z + 2) ^ 10 := by
      have hw : 1 - z ≠ 1 := fun h0 => by norm_num [mp sub_eq_self h0] at c
      have hz1 := norm_L_one_sub_le isPrimitive_one_level_one (w := 1 - z) (by simp
                                                                               linarith) (by simp
                                                                                             linarith) (inr hw)
      simp [aim] at hz1
      have hw1 : ‖1 - z‖ ≤ 3 * (aim z + 2) := by
        have := norm_le_abs_re_add_abs_im (1 - z)
        simp at this
        grind
      have hzw : ‖riemannZeta (1 - z)‖ ≤ 15 * (aim z + 2) ^ 2 := by
        rw [riemannZeta_eq_inv_sub_add hw, sub_sub_cancel_left]
        grw [norm_add_le, norm_inv, norm_neg, inv_anti₀ (by norm_num) c, chk_zeta0Bound (s := 1 - z) (by simp
                                                                                                         linarith), hw1]
        norm_num
        nlinarith [abs_nonneg (im z)]
      have hne : z ≠ 1 := by grind [one_re]
      rw [show riemannZeta₁ z = (z - 1) * riemannZeta z by rw [riemannZeta_eq_inv_sub_mul hne, mul_inv_cancel_left₀ (sub_ne_zero.2 hne)], norm_mul, norm_sub_rev]
      grw [hz1, hzw, hw1, show aim z + 7 ≤ 4 * (aim z + 2) by linarith [abs_nonneg (im z)]]
      ring_nf
      gcongr <;> norm_num
    by_cases hr : 0.5 ≤ re s
    · grw [hzR hr h2, pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 10)]
      gcongr
      norm_num
    · by_cases hn : 0.5 ≤ norm s
      · grw [hzL h1 (mp not_le hr) hn]
        gcongr <;> norm_num
      · grw [norm_le_of_forall_mem_frontier_norm_le (C := 2 ^ 31 * (2.5 : ℝ) ^ 10) isBounded_ball differentiable_riemannZeta₁.differentiableOn.diffContOnCl (fun z hz => by
            rw [frontier_ball (0 : ℂ) (by norm_num), mem_sphere_zero_iff_norm] at hz
            have ⟨hr1, hr2⟩ := mp abs_le (hz ▸ abs_re_le_norm z)
            have hiz : aim z ≤ 0.5 := hz ▸ abs_im_le_norm z
            rcases lt_or_ge (re z) 0.5 with hlt | hge
            · grw [hzL (by linarith) hlt (by rw [hz])]
              gcongr
              linarith
            · grw [hzR hge (by linarith), hiz]
              norm_num)
            (subset_closure (mpr mem_ball_zero_iff (mp not_le hn))),
          ← hY]
        norm_num
  · simp [Lent, hc]
    by_cases hr : 0.5 ≤ re s
    · nlinarith [chk_lBoundRight hc hr h2, le_self_pow₀ (by nlinarith [one_le_N N] : 1 ≤ rN N * Y) (by norm_num : 10 ≠ 0)]
    · have hw1 : 0.5 ≤ re (1 - s) := by
        simp
        linarith
      have hL1 := norm_L_one_sub_le hpx hw1 (by simp
                                                linarith) (inl (χ.map_zero' (ne_one_of_ne_one hc)))
      rw [sub_sub_cancel] at hL1
      simp [aim] at hL1
      have hL2 := chk_lBoundRight (mpr inv_ne_one hc) hw1 (by simp
                                                              linarith)
      simp [aim] at hL2
      grw [hL1, hL2, show aim s + 7 ≤ 4 * Y by linarith]
      have : (N : ℝ) ^ 6 * Y ^ 8 ≤ (N * Y) ^ 10 := by
        rw [mul_pow]
        gcongr <;> nlinarith [one_le_N N]
      nlinarith [pow_nonneg (by positivity : 0 ≤ rN N * Y) 10]

lemma Lent_local t :
    let c := cpx 2 t
    ∃ Z : Finset ℂ, (∀ ρ, ρ ∈ Z ↔ ρ ∈ closedBall c 3 ∧ Lent χ ρ = 0) ∧
      ZerosNear χ t ⊆ (Z : Set ℂ) ∧
      (∑ ρ ∈ Z, mR χ ρ) ≤ 132 * LN N t ∧
      ∀ s ∈ closedBall c 2.5, Lent χ s ≠ 0 →
        ‖logDeriv (Lent χ) s - ∑ ρ ∈ Z, mC χ ρ / (s - ρ)‖ ≤ 5808 * LN N t := by
  intro c0
  set X := rN N * (abs t + 2)
  set B := (2 : ℝ) ^ 56 * X ^ 10
  set M := log B
  let f := Lent χ
  let B6 := closedBall c0 6
  let B3 := closedBall c0 3
  let O3 := ball c0 3
  have h2arg : 2 ≤ X := by nlinarith [one_le_N N, abs_nonneg t]
  have := one_le_pow₀ (n := 10) (by linarith : 1 ≤ X)
  have hhalf : 0.5 ≤ ‖f c0‖ := by
    have hs1 : 1 < re c0 := by simp [c0]
    have hL2 : 0.5 ≤ ‖LFunction χ c0‖ := by
      have hmul := congrArg norm (DirichletCharacter.LSeries.mul_mu_eq_one χ hs1)
      rw [norm_mul, norm_one, ← LFunction_eq_LSeries χ hs1] at hmul
      have hS1 := (mpr LSeriesSummable_one_iff hs1).norm
      have : ‖LSeries ((fun n : ℕ => χ n) * fun n => (moebius n : ℂ)) c0‖ ≤ 2 := by
        refine le_trans (tsum_of_norm_bounded hS1.hasSum fun n => norm_term_le c0 (by
          simp
          grw [norm_le_one χ _]
          simp
          exact_mod_cast abs_moebius_le_one)) ?_
        simp_rw [hS1.tsum_eq_zero_add, norm_term_eq]
        simpa [c0, ← rpow_neg (cast_nonneg _)] using le_trans (tsum_rpow_le one_lt_two) (by norm_num)
      nlinarith [norm_nonneg (LFunction χ c0)]
    by_cases h : χ = 1
    · dsimp [f]
      rw [Lent_one_apply h (by grind [one_re]), norm_mul]
      have := re_le_norm (c0 - 1)
      simp [c0] at this
      nlinarith
    · simpa [f, Lent, h] using hL2
  have hf0 : f c0 ≠ 0 := by grind [norm_zero]
  have hM := log_pos (by nlinarith : 1 < B)
  have hMle : M ≤ 66 * LN N t := by
    dsimp [M, B, LN]
    rw [log_mul (by positivity) (by positivity), log_pow, log_pow]
    push_cast
    linarith [log_le_log two_pos h2arg]
  have hb z (hz : z ∈ B6) : ‖f z‖ ≤ B * ‖f c0‖ := by
    rw [mem_closedBall_iff_norm] at hz
    have := abs_re_le_norm (z - c0)
    have := abs_im_le_norm (z - c0)
    simp [c0] at *
    grw [lGrowth hpx (by grind) (by grind), show aim z + 2 ≤ 4 * (abs t + 2) by grind]
    rw [mul_left_comm, mul_pow]
    nlinarith
  have hsub6 := closedBall_subset_closedBall (x := c0) (by norm_num : (3 : ℝ) ≤ 6)
  obtain ⟨Zall, g, hZall, hg, hg0, hfac0⟩ := extract_zeros_Lent χ (isCompact_closedBall c0 6) (convex_closedBall c0 6).isPreconnected ⟨c0, mem_closedBall_self (by norm_num), c0 + 6, by simp, by simp⟩
  set Z := Zall.filter (· ∈ B3)
  let h z := (∏ ρ ∈ Zall.filter (· ∉ B3), (z - ρ) ^ mult χ ρ) * g z
  have hZ ρ : ρ ∈ Z ↔ ρ ∈ B3 ∧ f ρ = 0 := by
    simp [Z, hZall, B3]
    grind
  have hh : AnalyticOnNhd ℂ h B6 := fun z hz => (analyticAt_fun_prod _ fun _ _ => by fun_prop).mul (hg z hz)
  have hh0 {z} (hz : z ∈ B3) : h z ≠ 0 := mul_ne_zero (mpr prod_ne_zero_iff fun ρ hrx => pow_ne_zero _ (sub_ne_zero_of_ne fun e => (mp mem_filter hrx).2 (e ▸ hz))) (hg0 z (hsub6 hz))
  have hfac z (hz : z ∈ B6) : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ mult χ ρ) * h w :=
    (hfac0 z hz).trans (of_forall fun w => by
      dsimp
      rw [← mul_assoc, prod_filter_mul_prod_filter_not Zall (· ∈ B3)])
  have hh_le z (hz : z ∈ B6) : ‖h z‖ ≤ B * ‖h c0‖ := by
    refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hh.differentiableOn.diffContOnCl_ball subset_rfl) (fun w hw => ?_) (by rwa [closure_ball c0 (by norm_num)])
    rw [frontier_ball c0 (by norm_num), mem_sphere_iff_norm] at hw
    have hw6 := mpr mem_closedBall_iff_norm hw.le
    have hρ ρ (hrx : ρ ∈ Z) := mp mem_closedBall_iff_norm (mp (hZ ρ) hrx).1
    have hlow ρ (hrx : ρ ∈ Z) : 3 ≤ ‖w - ρ‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub w ρ c0, hρ ρ hrx]
    have hbw := hb w hw6
    rw [(hfac w hw6).eq_of_nhds, (hfac c0 (mem_closedBall_self (by norm_num))).eq_of_nhds] at hbw
    simp at hbw
    exact le_of_mul_le_mul_left (le_trans hbw (by
      rw [mul_left_comm]
      gcongr with ρ hrx
      rw [norm_sub_rev]
      linarith [hρ ρ hrx, hlow ρ hrx]))
      (prod_pos fun ρ hrx => pow_pos (by linarith [hlow ρ hrx]) _)
  refine ⟨Z, hZ, fun ρ ⟨h0, h1, him, hL⟩ => mpr (hZ ρ) ⟨by
    rw [mem_closedBall_iff_norm]
    have := norm_le_abs_re_add_abs_im (ρ - c0)
    simp [c0] at this
    grind,
    mpr (Lent_eq_zero_iff (by grind [one_re])) hL⟩, ?_, fun s hs hfs => ?_⟩
  · refine le_trans ?_ (le_trans ((analytic_Lent χ).sum_divisor_le (c := c0) (r := 3) (R := 6) (M := B * ‖f c0‖)
      (by norm_num) (by norm_num) (by nlinarith) hf0 fun z hz => hb z (sphere_subset_closedBall (by simpa using hz))) ?_)
    · rw [abs_of_pos three_pos, finsum_eq_sum_of_support_subset _ fun u hu => by
        have hu' := (divisor f _).supportWithinDomain hu
        exact mpr (hZ u) ⟨hu', mp (div_Lent_ne_zero hu') (mp mem_support hu)⟩]
      push_cast
      exact sum_le_sum fun u hu => by
        obtain ⟨hB3, hf0'⟩ := mp (hZ u) hu
        rw [div_Lent hB3, order_Lent fun e => Lent_one_ne_zero χ (e ▸ hf0')]
        simp [mR, mult]
    · have := half_le_log (x := 6 / 3)
      rw [mul_div_cancel_right₀ _ (mpr norm_ne_zero_iff hf0), div_le_iff₀ (by linarith)]
      nlinarith
  have hs3 : s ∈ O3 := closedBall_subset_ball (by norm_num) hs
  have hsR := hsub6 (ball_subset_closedBall hs3)
  rw [logDeriv_prod_factor (hfac s hsR) (fun ρ hrx h0 => hfs (mp sub_eq_zero h0 ▸ (mp (hZ ρ) hrx).2))
    (hh0 (ball_subset_closedBall hs3)) (hh s hsR).differentiableAt, add_sub_cancel_right, logDeriv_apply]
  have hhd := hh.differentiableOn.mono (ball_subset_closedBall.trans hsub6)
  have hneB z (hz : z ∈ O3) := hh0 (ball_subset_closedBall hz)
  obtain ⟨L, hL0, hLd⟩ := ((hhd.deriv isOpen_ball).div hhd hneB).isExactOn_ball.with_val_at c0 0
  have hLd_diff : DifferentiableOn ℂ L O3 := fun z hz => (hLd z hz).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc0, hfg⟩ := mp (logDeriv_eqOn_iff hhd hLd_diff.cexp isOpen_ball isPreconnected_ball (by simp) hneB)
    fun z hz' => by simp [logDeriv_apply, (hLd z hz').cexp.deriv]
  have hmem u (hu : u ∈ ball (0 : ℂ) 3) : c0 + u ∈ O3 := by simpa [O3, mem_ball_iff_norm] using hu
  have hsub1 : closedBall s 0.25 ⊆ closedBall c0 2.75 := closedBall_subset_closedBall' (by linarith [mp mem_closedBall hs])
  have hc := norm_deriv_le_of_forall_mem_sphere_norm_le (C := 22 * M) (by norm_num)
    (hLd_diff.diffContOnCl_ball (hsub1.trans (closedBall_subset_ball (by norm_num)))) fun x hx => by
      have hx' := mp mem_closedBall_iff_norm (hsub1 (sphere_subset_closedBall hx))
      have h1 := borelCaratheodory_zero hM (hLd_diff.comp (differentiableOn_id.const_add c0) hmem) (fun u hu =>
        mpr (le_log_iff_exp_le (by positivity)) (by
          simpa [hfg (hmem u hu), hfg (mem_ball_self three_pos), hL0, norm_exp, mul_comm B, mpr norm_pos_iff hc0] using
            hh_le (c0 + u) (hsub6 (ball_subset_closedBall (hmem u hu)))))
        three_pos (mpr mem_ball_zero_iff (by linarith)) (by simp [hL0])
      simp at h1
      grw [h1]
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  rw [(hLd s hs3).deriv] at hc
  norm_num [norm_div] at hc ⊢
  linarith

lemma zerosWindow t :
    (ZerosNear χ t).Finite ∧ ∑ᶠ ρ ∈ ZerosNear χ t, mR χ ρ ≤ 132 * LN N t := by
  obtain ⟨Z, -, hsub, hcnt, -⟩ := Lent_local hpx t
  have hfin := Z.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  grw [sum_le_sum_of_subset_of_nonneg (mpr (toFinset_subset (hs := hfin)) hsub) fun _ _ _ => cast_nonneg _, hcnt]

theorem localLemma {s}
    (h1 : -0.5 ≤ re s) (h2 : re s ≤ 3) (hLs : LFunction χ s ≠ 0) (hs1 : s ≠ 1) :
    ‖ldL χ s - (∑ᶠ ρ ∈ ZerosNear χ (im s), mC χ ρ / (s - ρ)) - eps0 χ / s + del1 χ / (s - 1)‖ ≤
      6200 * LN N (im s) := by
  set t := im s
  set c := cpx 2 t
  obtain ⟨Z, hZ, hsub, hcnt, hbound⟩ := Lent_local hpx t
  have hne1 {ρ} (h : ρ ∈ Z) : ρ ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ (mp (hZ ρ) h).2)
  have hb := hbound s (by
    rw [mem_closedBall_iff_norm]
    have := norm_le_abs_re_add_abs_im (s - c)
    simp [c, t] at this
    grind)
    fun h => hLs (mp (Lent_eq_zero_iff hs1) h)
  have hZN := Z.finite_toSet.subset hsub
  set E := (Z \ toFinset hZN).erase 0
  let F ρ := mC χ ρ / (s - ρ)
  let Z0 := if (0 : ℂ) ∈ Z then F 0 else 0
  have hdec : ∑ ρ ∈ Z, F ρ = (∑ᶠ ρ ∈ ZerosNear χ t, F ρ) + (∑ ρ ∈ E, F ρ) + Z0 := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hZN, ← sum_sdiff (mpr (toFinset_subset (hs := hZN)) hsub)]
    dsimp [Z0, E]
    split_ifs with hD
    · rw [← add_sum_erase _ _ (mpr mem_sdiff ⟨hD, by simp [ZerosNear]⟩)]
      ring
    · rw [erase_eq_of_notMem (by simp [hD])]
      ring
  have hfar : ‖∑ ρ ∈ E, F ρ‖ ≤ 264 * LN N t := by
    have hEsub : E ⊆ Z := (erase_subset _ _).trans sdiff_subset
    grw [norm_sum_le, sum_le_sum (g := fun ρ => 2 * mR χ ρ) fun ρ hrx => by
      obtain ⟨hne0, hrs⟩ := mp mem_erase hrx
      have hZρ := hEsub hrx
      obtain ⟨hBρ, hfρ⟩ := mp (hZ ρ) hZρ
      have hL := mp (Lent_eq_zero_iff (hne1 hZρ)) hfρ
      have hre := le_trans (abs_re_le_norm (ρ - c)) (mp mem_closedBall_iff_norm hBρ)
      simp [c] at hre
      have hd : 0.5 ≤ ‖s - ρ‖ := by
        rcases zeroLocus hpx (by grind) (hne1 hZρ) hL with ⟨a, b⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · by_contra hc
          exact (mp mem_sdiff hrs).2 (mpr (mem_toFinset hZN) ⟨a, b, by
            have := abs_im_le_norm (s - ρ)
            simp at this
            grind, hL⟩)
        · contradiction
        · have := re_le_norm (s - -1)
          simp [sub_neg_eq_add] at this ⊢
          linarith
      rw [norm_div, norm_natCast]
      grw [← hd]
      norm_num [mR, rN]
      linarith,
      ← mul_sum, sum_le_sum_of_subset_of_nonneg hEsub fun _ _ _ => cast_nonneg _, hcnt]
    linarith
  have hzero : ‖Z0 - eps0 χ / s‖ ≤ 1 := by
    dsimp [Z0]
    by_cases h0 : (0 : ℂ) ∈ Z
    · obtain ⟨he, h1⟩ := mp (L0_iff hpx) (mp (Lent_eq_zero_iff zero_ne_one) (mp (hZ 0) h0).2)
      simp [F, h0, mC, mult, (mult_zero_of_even hpx he h1).2, eps0, he, h1]
    · simp only [h0, ite_false, zero_sub, norm_neg, eps0]
      split_ifs with he
      · have h0' : 3 < norm c := mp not_le fun hb => h0 (mpr (hZ 0) ⟨by simpa [mem_closedBall_iff_norm] using hb, mpr (Lent_eq_zero_iff zero_ne_one) (mpr (L0_iff hpx) he)⟩)
        have := norm_le_abs_re_add_abs_im c
        simp [c] at this
        rw [norm_div, norm_one]
        exact div_le_one_of_le₀ (by linarith [abs_im_le_norm s]) (norm_nonneg _)
      · simp
  grw [nadd3 hb hfar hzero (by rw [logDeriv_Lent hs1 hLs, hdec]
                               ring1)]
  linarith [half_le_LN N t]

lemma sum_mult_le {T}
    B (hB : ∀ ρ ∈ B, ρ ∈ ZerosNear χ (T + 0.5) ∪ ZerosNear χ (-(T + 0.5))) (hT : 0 ≤ T := by linarith) :
    ∑ ρ ∈ B, mR χ ρ ≤ 264 * log (N * (T + 3)) := by
  obtain ⟨hf1, hw1⟩ := zerosWindow hpx (T + 0.5)
  obtain ⟨hf2, hw2⟩ := zerosWindow hpx (-(T + 0.5))
  have h1 : _ ≤ (∑ ρ ∈ toFinset hf1, mR χ ρ) + ∑ ρ ∈ toFinset hf2, mR χ ρ :=
    le_trans (sum_le_sum_of_subset_of_nonneg (fun x hx => by simpa using hB x hx : B ⊆ toFinset hf1 ∪ toFinset hf2) fun _ _ _ => cast_nonneg _)
      (by rw [← sum_union_inter]
          exact le_add_of_nonneg_right (sum_nonneg fun _ _ => cast_nonneg _))
  rw [← finsum_mem_eq_finite_toFinset_sum _ hf1, ← finsum_mem_eq_finite_toFinset_sum _ hf2] at h1
  simp only [LN, abs_neg, abs_of_nonneg (by linarith : 0 ≤ T + 0.5)] at hw1 hw2
  have := one_le_N N
  have : log (N * (T + 0.5 + 2)) ≤ log (N * (T + 3)) := log_le_log (by nlinarith) (by nlinarith)
  linarith

theorem goodHeightExists {T} (hT : 2 ≤ T) :
    ∃ T', T ≤ T' ∧ T' ≤ T + 1 ∧ GoodHeight χ T' := by
  let th := T + 0.5
  set LT := log (N * (T + 3))
  have hN1 := one_le_N N
  have hU := (zerosWindow hpx th).1.union (zerosWindow hpx (-th)).1
  set S := (toFinset hU).image aim
  have : rN (card S) ≤ 264 * LT := by
    grw [show rN (card S) ≤ card (toFinset hU) by exact_mod_cast card_image_le,
      ← sum_mult_le hpx _ fun _ => mp (mem_toFinset hU)]
    rw [card_eq_sum_ones, cast_sum]
    exact sum_le_sum fun ρ hrx => by
      rcases mp (mem_toFinset hU) hrx with ⟨-, h1, -, hL⟩ | ⟨-, h1, -, hL⟩ <;>
        (have hne : ρ ≠ 1 := by grind [one_re]
         exact_mod_cast mpr one_le_iff_ne_zero (by
           rw [mult, ← order_Lent hne, ← natCast_ne_zero, ← div_Lent (mem_univ ρ), div_Lent_ne_zero (mem_univ ρ), Lent_eq_zero_iff hne]
           exact hL))
  let K := rN (card S) + 1
  have hK : 0 < K := by positivity
  obtain ⟨T', ⟨hT1, hT2⟩, hfar⟩ : ∃ x ∈ Icc T (T + 1), ∀ y ∈ S, inv (2 * K) ≤ abs (x - y) := by
    by_contra hcon
    push Not at hcon
    choose! g hgS hgd using fun i (hi : i ∈ range (card S + 2)) => hcon (T + i / K) ⟨le_add_of_nonneg_right (by positivity),
      by linarith [mpr (div_le_one hK) (show rN i ≤ K by dsimp [K]
                                                         exact_mod_cast mp lt_succ_iff (mp mem_range hi))]⟩
    obtain ⟨i, hi, j, hj, hij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (s := range (card S + 2)) (by simp) hgS
    have : inv K ≤ abs ((T + i / K) - (T + j / K)) := by
      rw [add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_pos hK, inv_eq_one_div]
      gcongr
      exact_mod_cast one_le_abs (sub_ne_zero_of_ne (by exact_mod_cast hij : (i : ℤ) ≠ j))
    have : 2 * inv (2 * K) = inv K := by field
    grind [heq ▸ hgd i hi, hgd j hj]
  have := half_le_log (x := rN N * T')
  have : LT ≤ 3 * log (N * T') := by
    simpa [LT, log_pow] using log_le_log (by positivity) (by
      rw [mul_pow]
      gcongr
      · exact le_self_pow₀ hN1 three_ne_zero
      · nlinarith [sq_nonneg (T' - 2)] : rN N * (T + 3) ≤ (rN N * T') ^ 3)
  refine ⟨T', hT1, hT2, fun ρ h0 h1 hL => ?_⟩
  let M := 2 * (264 * LT + 1)
  have : 0 ≤ LT := log_nonneg (by nlinarith)
  grw [inv_anti₀ (by positivity) (by linarith : M ≤ 1600 * log (N * T'))]
  by_cases hw : abs (aim ρ - th) ≤ 1
  · rw [abs_sub_comm]
    exact le_trans (inv_anti₀ (by positivity) (by dsimp [M, K]
                                                  linarith)) (hfar (aim ρ) (mem_image_of_mem _ (mpr (mem_toFinset hU) (mem_window h0 h1 hL hw))))
  · grind [inv_anti₀ two_pos (by linarith : 2 ≤ M)]

lemma norm_logDeriv_le {s}
    (h1 : -0.5 ≤ re s) (h2 : re s ≤ 3) (hs0 : 0.5 ≤ norm s) (hs1 : 0.5 ≤ ‖s - 1‖)
    {d} (hd : 0 < d) (h : ∀ ρ ∈ ZerosNear χ (im s), d ≤ ‖s - ρ‖) :
    ‖ldL χ s‖ ≤ 6206 * LN N (im s) + 132 * LN N (im s) / d := by
  have hne1 : s ≠ 1 := fun h => by norm_num [h] at hs1
  have h0 : LFunction χ s ≠ 0 := fun hL => by
    have ⟨a, b⟩ := zeroStrip hpx h1 (by grind [norm_zero]) hne1 hL
    have := h s ⟨a, b, by simp, hL⟩
    simp at this
    linarith
  obtain ⟨hf, hfw⟩ := zerosWindow hpx (im s)
  rw [finsum_mem_eq_finite_toFinset_sum _ hf] at hfw
  have hsum : ‖∑ᶠ ρ ∈ ZerosNear χ (im s), mC χ ρ / (s - ρ)‖ ≤ 132 * LN N (im s) / d := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    grw [norm_sum_le, sum_le_sum (g := fun ρ => mR χ ρ / d) fun ρ hrx => by
      rw [norm_div, norm_natCast]
      gcongr
      exact h ρ (mp (mem_toFinset hf) hrx), ← sum_div]
    gcongr
  have hq {c z : ℂ} (hc : norm c ≤ 1) (hz : 0.5 ≤ norm z) : ‖c / z‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith
  grw [nadd3 (nadd2 (localLemma hpx h1 h2 h0 hne1) hsum rfl) (hq norm_eps0 hs0) (nneg (hq norm_del1 hs1))]
  linarith [half_le_LN N (im s)]
end PrimSec

lemma one_lt_cLine {u} (hu : 2 ≤ u) : 1 < cLine u := by
  rw [cLine]
  linarith [mpr inv_pos <| log_pos <| by linarith]

lemma cLine_le_three {u} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  rw [cLine]
  have := half_le_log hu
  grw [inv_anti₀ (by norm_num) this]
  norm_num

section RectSec
variable {x0 x1 y0 y1 : ℝ}

def rectBdry (x0 x1 y0 y1 : ℝ) : Set ℂ :=
  {s | (re s ∈ uIcc x0 x1 ∧ (im s = y0 ∨ im s = y1)) ∨ (im s ∈ uIcc y0 y1 ∧ (re s = x0 ∨ re s = x1))}

def rectOpen (x0 x1 y0 y1 : ℝ) : Set ℂ :=
  {s | x0 < re s ∧ re s < x1 ∧ y0 < im s ∧ im s < y1}

lemma bdryH {x y} (hx : x ∈ uIcc x0 x1) (hy : y = y0 ∨ y = y1) : cpx x y ∈ rectBdry x0 x1 y0 y1 :=
  inl ⟨by simpa using hx, by simpa using hy⟩

lemma bdryV {x y} (hy : y ∈ uIcc y0 y1) (hx : x = x0 ∨ x = x1) : cpx x y ∈ rectBdry x0 x1 y0 y1 :=
  inr ⟨by simpa using hy, by simpa using hx⟩

lemma hdH y x : HasDerivAt (cpx · y) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp.add_const (cR y * I)

lemma hdV x y : HasDerivAt (cpx x ·) I y := by simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (cR x)

lemma seg {F f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {d : ℂ} {s : Set ℂ} (hγ : ∀ t, HasDerivAt γ d t)
    (h : ∀ t ∈ uIcc a b, HasDerivAt F (f (γ t)) (γ t)) (hc : ContinuousOn f s) (hs : ∀ t ∈ uIcc a b, γ t ∈ s) :
    d • ∫ t in a..b, f (γ t) = F (γ b) - F (γ a) := by
  rw [← integral_smul]
  exact integral_eq_sub_of_hasDerivAt (fun t ht => ((h t ht).comp t (hγ t)).congr_deriv (mul_comm _ _))
    ((hc.comp (fun t _ => (hγ t).continuousAt.continuousWithinAt) hs).const_smul d).intervalIntegrable

lemma bdry_ne {s p} (hs : s ∈ rectBdry x0 x1 y0 y1) (hp : p ∈ rectOpen x0 x1 y0 y1) : s ≠ p := by
  rintro rfl
  grind [rectBdry, rectOpen]

lemma bdry_sub (hre : x0 ≤ x1 := by linarith) (him : y0 ≤ y1 := by linarith) : rectBdry x0 x1 y0 y1 ⊆ rect x0 x1 y0 y1 := by
  rintro s (⟨hr, hi | hi⟩ | ⟨hi, hr | hr⟩) <;> rw [uIcc_of_le (by assumption)] at * <;> simp_all [rect, mem_reProdIm]

lemma closed_nhds {p} (hp : p ∈ rectOpen x0 x1 y0 y1) : rect x0 x1 y0 y1 ∈ 𝓝 p := by
  obtain ⟨a, b, c, d⟩ := hp
  exact mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds ⟨⟨a, b⟩, c, d⟩) fun _ h => ⟨Ioo_subset_Icc_self h.1, Ioo_subset_Icc_self h.2⟩

lemma rectInt_congr {f g} (h : EqOn f g (rectBdry x0 x1 y0 y1)) : rectInt f x0 x1 y0 y1 = rectInt g x0 x1 y0 y1 := by
  simp only [rectInt]
  rw [integral_congr fun _ hx => h (bdryH hx (inl rfl)), integral_congr fun _ hx => h (bdryH hx (inr rfl)),
    integral_congr fun _ hy => h (bdryV hy (inr rfl)), integral_congr fun _ hy => h (bdryV hy (inl rfl))]

lemma rectInt_add {f g} (hf : ContinuousOn f (rectBdry x0 x1 y0 y1)) (hg : ContinuousOn g (rectBdry x0 x1 y0 y1)) :
    rectInt (fun s => f s + g s) x0 x1 y0 y1 = rectInt f x0 x1 y0 y1 + rectInt g x0 x1 y0 y1 := by
  have bi {γ : ℝ → ℂ} {a b} (h : ∀ t ∈ uIcc a b, γ t ∈ rectBdry x0 x1 y0 y1) (hγ : Continuous γ := by fun_prop) :
      ∫ t in a..b, (f (γ t) + g (γ t)) = (∫ t in a..b, f (γ t)) + ∫ t in a..b, g (γ t) :=
    integral_add ((hf.comp hγ.continuousOn h).intervalIntegrable (μ := volume)) ((hg.comp hγ.continuousOn h).intervalIntegrable (μ := volume))
  simp [rectInt, bi fun _ hx => bdryH hx (inl rfl), bi fun _ hx => bdryH hx (inr rfl),
    bi fun _ hy => bdryV hy (inr rfl), bi fun _ hy => bdryV hy (inl rfl)]
  ring

lemma rectInt_const_mul (c f) : rectInt (fun s => c * f s) x0 x1 y0 y1 = c * rectInt f x0 x1 y0 y1 := by
  simp [rectInt]
  ring

lemma rectInt_div_sub {h p} (hp : p ∈ rectOpen x0 x1 y0 y1) (hh : DifferentiableOn ℂ h (rect x0 x1 y0 y1)) :
    rectInt (fun s => h s / (s - p)) x0 x1 y0 y1 = τI * h p := by
  have ⟨h1, h2, h3, h4⟩ := hp
  have hd := mpr (differentiableOn_dslope (closed_nhds hp)) hh
  have hz : rectInt (dslope h p) x0 x1 y0 y1 = 0 :=
    integral_boundary_rect_eq_zero_of_differentiableOn _ ⟨x0, y0⟩ ⟨x1, y1⟩ (by rwa [uIcc_of_le (by linarith), uIcc_of_le (by linarith)])
  have hc : ContinuousOn (fun s => inv (s - p)) (rectBdry x0 x1 y0 y1) :=
    ContinuousOn.inv₀ (by fun_prop) fun _ hs => sub_ne_zero_of_ne (bdry_ne hs hp)
  have hinv_int : rectInt (fun s => inv (s - p)) x0 x1 y0 y1 = τI := by
    have hL {s} (hs : s - p ∈ slitPlane) : HasDerivAt (fun s => cl (s - p)) (inv (s - p)) s := by simpa using ((hasDerivAt_id s).sub_const p).clog hs
    have hH {y} (hy : y = y0 ∨ y = y1) (hy' : y - im p ≠ 0) :=
      seg (d := 1) (hdH y) (fun _ _ => hL (mpr mem_slitPlane_iff (inr (by simpa)))) hc fun _ hx => bdryH hx hy
    simp only [one_smul] at hH
    simp only [rectInt]
    rw [hH (inl rfl) (by linarith), hH (inr rfl) (by linarith),
      seg (hdV x1) (fun _ _ => hL (mpr mem_slitPlane_iff (inl (by
        simp
        linarith)))) hc fun _ hy => bdryV hy (inr rfl),
      seg (hdV x0) (fun _ _ => (((hasDerivAt_id _).const_sub p).clog (mpr mem_slitPlane_iff (inl (by
        simp
        linarith)))).congr_deriv (by
        rw [neg_div, ← div_neg, neg_sub, one_div]
        rfl)) hc fun _ hy => bdryV hy (inl rfl)]
    simp only [cl, id, ← neg_sub (cpx x0 y1), ← neg_sub (cpx x0 y0)]
    set a := cpx x0 y1 - p
    set b := cpx x0 y0 - p
    have e1 := arg_neg_eq_arg_sub_pi_of_im_pos (x := a) (by
      simp [a]
      linarith)
    have e2 := arg_neg_eq_arg_add_pi_of_im_neg (x := b) (by
      simp [b]
      linarith)
    apply cext <;> simp [τI, log_re, log_im, e1, e2] <;> ring1
  rw [rectInt_congr (g := fun s => dslope h p s + h p * inv (s - p)) fun s hs => by
        have hne := bdry_ne hs hp
        dsimp
        rw [dslope_of_ne _ hne, slope_def_field]
        field [sub_ne_zero_of_ne hne],
    rectInt_add (hd.continuousOn.mono bdry_sub) (hc.const_mul (h p)), hz, rectInt_const_mul, hinv_int]
  ring
end RectSec

section KernelSec

theorem perron_kernel_single_term {y c T} (hy : 0 < y) (hc : 1 ≤ c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  set l := log y
  set E := y ^ c
  let ker (s : ℂ) := cexp (↑l * s) / s
  set J := ∫ t in -T..T, ker (cpx c t)
  have hEe : E = rexp (l * c) := rpow_def_of_pos hy c
  have hE0 := hEe ▸ exp_pos _
  suffices hJ : ‖J - if 1 ≤ y then τ else 0‖ ≤ 2 * π * E * kb T y by
    rw [show (if 1 ≤ y then (1 : ℂ) else 0) = inv τ * if 1 ≤ y then τ else 0 by
          split_ifs <;> simp [τ]
          field_simp [pi_ne_zero],
      show perronK y c T = inv τ * J from congrArg _ (integral_congr fun _ _ => by
        simp [ker, cpow_def_of_ne_zero (mpr ofReal_ne_zero hy.ne'), ← ofReal_log hy.le, l]),
      ← mul_sub, norm_mul]
    grw [hJ]
    simp
    exact le_of_eq (by field)
  have hker x y : ‖ker (cpx x y)‖ = rexp (l * x) / ‖cpx x y‖ := by simp [ker, norm_exp]
  have hT0 := hT.le
  have hars0 := mpr arsinh_nonneg_iff hT0
  have h1 : ‖J - if 1 ≤ y then τ else 0‖ ≤ 2 * π * E * (1 + arsinh T) := by
    grw [norm_sub_le, norm_int_inv_sqrt (C := E) hT0 fun t _ => by
      rw [hker, ← hEe, div_eq_mul_inv]
      gcongr
      rw [norm_add_mul_I]
      gcongr
      nlinarith]
    have := mul_nonneg hE0.le hars0
    split_ifs with hy1 <;> simp
    · nlinarith [pi_gt_three, one_le_rpow hy1 (by linarith : 0 ≤ c)]
    · nlinarith [pi_gt_three]
  by_cases hl : l = 0
  · simpa [kb, l, hl] using h1
  simp only [kb, show log y ≠ 0 from hl, ite_false]
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min h1 ?_
  set B := E / abs l / T
  have : 0 < B := by positivity
  set U := c + 1 + 2 * T / B
  have hcU : c < U := by linarith [show 0 < 2 * T / B by positivity]
  have hU0 : 0 < U := by linarith
  have hfin a b x (sgn : ℂ) {L : ℂ}
      (h : I * L = sgn * ((∫ t in a..b, ker (cpx t (-T))) - ∫ t in a..b, ker (cpx t T)) + I * ∫ t in -T..T, ker (cpx x t))
      (hab : a ≤ b := by linarith) (hm1 : l * a ≤ l * c := by nlinarith) (hm2 : l * b ≤ l * c := by nlinarith)
      (hlx : l * x ≤ 0 := by nlinarith) (hxU : abs x = U := by simp [hU0.le]) (hsgn : norm sgn = 1 := by simp) :
      norm L ≤ 2 * π * E * inv (T * abs l) := by
    have hh h (hh : abs h = T := by simp [hT0]) : ‖∫ t in a..b, ker (cpx t h)‖ ≤ B := by
      grw [norm_integral_le_of_norm_le (g := fun t => rexp (l * t) / abs h) hab (of_forall fun t _ => by
        rw [hker]
        gcongr
        exact hh ▸ hT
        simpa using abs_im_le_norm (cpx t h)) (Continuous.intervalIntegrable (by fun_prop) _ _)]
      rw [integral_div, integral_comp_mul_left rexp hl, integral_exp, smul_eq_mul, hh]
      simp only [B, hEe]
      grw [le_abs_self (inv l * _)]
      rw [abs_mul, abs_inv, ← div_eq_inv_mul]
      gcongr
      grind [exp_pos (l * b), exp_pos (l * a), mpr exp_le_exp hm1, mpr exp_le_exp hm2]
    have hv : ‖∫ t in -T..T, ker (cpx x t)‖ ≤ B := by
      grw [norm_integral_le_of_norm_le_const (C := rexp (l * x) / abs x) fun t _ => by
        rw [hker]
        gcongr
        exact hxU ▸ hU0
        simpa using abs_re_le_norm (cpx x t), mpr exp_le_one_iff hlx]
      rw [hxU, sub_neg_eq_add, abs_of_pos (by linarith)]
      dsimp [U]
      field_simp
      nlinarith
    rw [show norm L = ‖I * L‖ by simp, h]
    grw [norm_add_le, norm_mul, hsgn, one_mul, norm_sub_le, hh (-T), hh T, norm_mul, norm_I, one_mul, hv]
    dsimp [B]
    field_simp
    nlinarith [pi_gt_three, hE0]
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · have hrect := integral_boundary_rect_eq_zero_of_differentiableOn ker ⟨c, -T⟩ ⟨U, T⟩ fun z hz =>
      (DifferentiableAt.div (by fun_prop) differentiableAt_id fun h => by
        have := (uIcc_of_le hcU.le ▸ hz.1).1
        simp [h] at this
        linarith).differentiableWithinAt
    simp only [smul_eq_mul] at hrect
    rw [ite_eq_right (mpr not_le (mp (log_neg_iff hy) hneg)), sub_zero]
    exact hfin c U U 1 (by dsimp [J]
                           linear_combination -hrect)
  · have hrect := rectInt_div_sub (h := fun s => cexp (l * s)) (p := 0) (x0 := -U) (x1 := c) (y0 := -T) (y1 := T)
      (by simp [rectOpen]
          grind) (by fun_prop)
    simp [rectInt, τI] at hrect
    rw [ite_eq_left (mp (log_pos_iff hy.le) hpos).le]
    exact hfin (-U) c (-U) (-1) (by simp [ker, J] at *
                                    linear_combination hrect)

theorem perronSumBound {u T} (hu : 2 ≤ u) (hT : 2 ≤ T) (hTu : T ≤ 2 * u) :
    Summable (fun n => Λ n * (u / n) ^ cLine u * kb T (u / n)) ∧
    ∑' n, Λ n * (u / n) ^ cLine u * kb T (u / n) ≤ 1500 * (u * log u ^ 2 / T + log u) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  set L := log u
  have := half_le_log hu
  have := mpr arsinh_nonneg_iff hT0.le
  have hkb_nn y : 0 ≤ kb T y := by
    unfold kb
    split_ifs <;> positivity
  have hkb_le {y a} (ha : 0 < a) (h : a ≤ abs (log y)) : kb T y ≤ inv (T * a) := by
    unfold kb
    rw [ite_eq_right (by grind)]
    exact le_trans (min_le_right _ _) (inv_anti₀ (by positivity) (by gcongr))
  let pTerm n := Λ n * (u / n) ^ cLine u * kb T (u / n)
  have hp_nn n : 0 ≤ pTerm n := mul_nonneg (mul_nonneg vonMangoldt_nonneg (rpow_nonneg (by positivity) _)) (hkb_nn _)
  have hsumK K : ∑ n ∈ range K, pTerm n ≤ 1500 * (u * L ^ 2 / T + L) := by
    let P n := rN n ≤ u / 2 ∨ 2 * u ≤ n
    set SF2 := (range K).filter (¬P ·)
    rw [← sum_filter_add_sum_filter_not (range K) P pTerm]
    refine le_trans (add_le_add (b := 3 / 0.69 * u / T * (8 * L ^ 2)) (d := 16 * L * (2 + 8 * L + 2 * (6 * u * L / T))) ?_ ?_)
      (by field_simp
          nlinarith [sq_nonneg L, mul_le_mul_of_nonneg_right hTu (sq_nonneg L)])
    · have h2 : ∑ n ∈ range K, log n * rN n ^ (-cLine u) ≤ 8 * L ^ 2 := by
        set e := inv (2 * L)
        have hep : 0 < e := by positivity
        rw [show cLine u = 1 + 2 * e by rw [cLine]
                                        field]
        rcases K with _ | M
        · simp
          positivity
        rw [sum_range_succ', cast_zero, log_zero, zero_mul, add_zero]
        have hsr := mpr (summable_nat_add_iff 1) (mpr summable_nat_rpow (by linarith : -(e + 1) < -1))
        simp only [cast_add, cast_one] at hsr
        grw [sum_le_sum (g := fun i => (rN i + 1) ^ (-(e + 1)) / e) fun i _ => by
            push_cast
            grw [log_le_rpow_div (by positivity) hep]
            rw [div_mul_eq_mul_div, ← rpow_add (by positivity)]
            exact le_of_eq (by congr 2
                               ring),
          ← sum_div, hsr.sum_le_tsum (range M) fun _ _ => by positivity, tsum_rpow_le (by linarith)]
        simp [e]
        field_simp
        nlinarith
      grw [← h2, ← exp_one_lt_three.le]
      rw [mul_sum]
      refine le_trans (sum_le_sum fun n hn => ?_) (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity)
      rcases eq_zero_or_pos n with rfl | hnp
      · simp [pTerm]
      have hx : 0 < rN n := mpr cast_pos hnp
      have := hkb_nn (u / n)
      dsimp [pTerm]
      grw [vonMangoldt_le_log, hkb_le (a := 0.69) (by norm_num) (by
        rcases (mp mem_filter hn).2 with h | h
        · exact le_trans (half_le_log (mpr (le_div_iff₀ hx) (by linarith))) (le_abs_self _)
        · rw [← abs_neg, ← log_inv, inv_div]
          exact le_trans (half_le_log (mpr (le_div_iff₀ hu0) (by linarith))) (le_abs_self _))]
      rw [div_rpow hu0.le hx.le, rpow_neg hx.le, rpow_cLine hu]
      exact le_of_eq (by field)
    · have hS2 n (hn : n ∈ SF2) : u / 2 < n ∧ rN n < 2 * u := by simpa [SF2, P, not_or] using (mp mem_filter hn).2
      let f n := if n ∈ SF2 then kb T (u / n) else 0
      grw [sum_le_sum (g := fun n => 16 * L * f n) fun n hn => by
        obtain ⟨hgt, hlt⟩ := hS2 n hn
        have hx : 0 < rN n := by linarith
        have := hkb_nn (u / n)
        dsimp [pTerm, f]
        rw [ite_eq_left hn]
        grw [vonMangoldt_le_log, log_le_2log (by nlinarith : rN n ≤ u ^ 2), mpr (div_le_iff₀ hx) (by linarith : u ≤ 2 * n), cLine_le_three hu]
        · linarith
        · norm_num
        · linarith [one_lt_cLine hu], ← mul_sum]
      gcongr
      set n0 := ⌊u⌋₊
      have f1 := floor_le hu0.le
      have : arsinh T ≤ 4 * L := by
        grw [arsinh_le_log, show 1 + 2 * T ≤ u ^ 4 by nlinarith [sq_nonneg (u - 2)]]
        simp [L, log_pow]
      have hf6 m : f m ≤ 1 + 4 * L := by
        dsimp [f, kb]
        split_ifs <;> (try grw [min_le_left]) <;> linarith
      have hhar : ∑ j ∈ range n0, inv (rN j + 1) ≤ 3 * L := by
        have h1 := harmonic_le_one_add_log n0
        simp [harmonic] at h1
        linarith [log_le_log (by exact_mod_cast mpr floor_pos (by linarith)) f1]
      have hstep (g : ℕ → ℕ) (hg : ∀ j ∈ range n0, rN j + 1 ≤ abs (u - g j)) : ∑ j ∈ range n0, f (g j) ≤ 6 * u * L / T := by
        have hl {a b} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (ha2 : a ≤ 2 * u := by linarith) : (a - b) / (2 * u) ≤ abs (log (a / b)) := by
          grw [← le_abs_self _, ← one_sub_inv_le_log_of_pos (div_pos ha hb)]
          rw [inv_div, ← div_self ha.ne', ← sub_div]
          gcongr
        rw [show 6 * u * L / T = 2 * u / T * (3 * L) by ring]
        grw [← hhar]
        rw [mul_sum]
        refine sum_le_sum fun j hj => ?_
        dsimp [f]
        split_ifs with hm
        · obtain ⟨hx1, hx2⟩ := hS2 _ hm
          have hx : 0 < rN (g j) := by linarith
          refine trans_eq (hkb_le (a := (rN j + 1) / (2 * u)) (by positivity) ?_) (by field)
          rcases le_or_gt (rN (g j)) u with hxu | hxu
          · grw [hg j hj, abs_of_nonneg (by linarith), hl hu0 hx hxu]
          · rw [← abs_neg, ← log_inv, inv_div]
            grw [hg j hj, abs_sub_comm, abs_of_pos (by linarith), hl hx hu0 hxu.le]
        · positivity
      grw [sum_le_sum_of_subset_of_nonneg (t := range (n0 + (n0 + 2)))
        (fun n hn => mpr mem_range (mp (cast_lt (α := ℝ)) (by
          push_cast
          linarith [(hS2 n hn).2, lt_floor_add_one u]))) fun _ _ _ => by
          dsimp [f]
          split_ifs
          exacts [hkb_nn _, le_rfl]]
      rw [sum_range_add, sum_range_succ', sum_range_succ', ← sum_range_reflect f n0]
      linarith [hf6 (n0 + 0), hf6 (n0 + (0 + 1)),
        hstep (fun j => n0 - 1 - j) fun j hj => by
          have := mp mem_range hj
          grw [← le_abs_self _]
          dsimp [rN]
          rw [cast_sub (by omega), cast_sub (by omega)]
          simp
          linarith,
        hstep (fun j => n0 + (j + 1 + 1)) fun j _ => by
          grw [← neg_le_abs _]
          push_cast
          linarith [lt_floor_add_one u]]
  exact ⟨summable_of_sum_range_le hp_nn hsumK, tsum_le_of_sum_range_le hp_nn hsumK⟩
end KernelSec

section SidesSec
variable {u T T' : ℝ} (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T') (hT'1 : T' ≤ T + 1)
include hT hTu hTT' hT'1

theorem perronL :
    ‖psiRaw χ u - vertInt χ u T'‖ ≤ 1500 * Err N u T := by
  have hu := le_trans hT hTu
  have hc1 := one_lt_cLine hu
  set c := cLine u
  have hu0 : 0 < u := by linarith
  let a : ℕ → ℂ := (fun n : ℕ => χ n) * fun n => (Λ n : ℂ)
  have ha n : ‖a n‖ ≤ Λ n := by simpa [a, abs_of_nonneg vonMangoldt_nonneg] using mul_le_of_le_one_left vonMangoldt_nonneg (norm_le_one χ _)
  have ha0 := mp norm_le_zero_iff (by simpa using ha 0)
  obtain ⟨hSs, hSle⟩ := perronSumBound hu (le_trans hT hTT') (by linarith)
  have hLsum := (LSeriesSummable_vonMangoldt (s := c) (by simpa using hc1)).norm
  let z t := cpx c t
  let K t := (u : ℂ) ^ z t / z t
  have hterm n t : ‖term a (z t) n‖ ≤ ‖term (fun k => (Λ k : ℂ)) c n‖ := by
    simp [norm_term_eq, z]
    split_ifs
    · rfl
    · grw [ha n, ← le_abs_self]
  have hDC := hasSum_integral_of_dominated_convergence (μ := volume) (a := -T') (b := T')
    (F := fun n t => term a (z t) n * K t) (f := fun t => LSeries a (z t) * K t) (fun n _ => ‖term (fun k => (Λ k : ℂ)) c n‖ * (u ^ c / c))
    (fun n => Measurable.aestronglyMeasurable (by by_cases hn : n = 0 <;> simp [term, hn]
                                                  fun_prop))
    (fun n => of_forall fun t _ => by
      grw [norm_mul, hterm n t, norm_div, norm_cpow_eq_rpow_re_of_pos hu0]
      simp [z]
      gcongr
      simpa [z] using re_le_norm (z t))
    (of_forall fun _ _ => hLsum.mul_right _) intervalIntegrable_const
    (of_forall fun t _ => (Summable.of_norm_bounded hLsum fun n => hterm n t).hasSum.mul_right _)
  have hEq n : a n * perronK (u / n) c T' = inv τ * ∫ t in (-T')..T', term a (z t) n * K t := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    rw [perronK, mul_left_comm, ← integral_const_mul]
    congr 2
    funext t
    rw [term_of_ne_zero hn, ofReal_div, div_cpow_ofReal_nonneg hu0.le n.cast_nonneg]
    push_cast
    ring
  have hG := hDC.mul_left (inv τ)
  simp_rw [← hEq] at hG
  have hind : HasSum (fun n => a n * if 1 ≤ u / n then 1 else 0) (psiRaw χ u) := by
    rw [psiRaw, sum_congr rfl fun n hn => ?_]
    · exact hasSum_sum_of_ne_finset_zero fun n hn => by
        rw [mem_Icc, not_and_or] at hn
        rcases hn with hn | hn
        · simp [show n = 0 by omega, ha0]
        · have : u < n := lt_of_floor_lt (mp not_le hn)
          simp [mpr not_le (mpr (div_lt_one (by linarith)) this)]
    · rw [mem_Icc] at hn
      simp [a, mpr (one_le_div (mpr cast_pos hn.1)) (le_trans (mpr cast_le hn.2) (floor_le hu0.le)), mul_comm]
  have hint t : LSeries a (z t) = -ldL χ (z t) := by
    have hs : 1 < re (z t) := by simpa [z] using hc1
    simp only [a, LSeries_twist_vonMangoldt_eq χ hs, ldL, logDeriv_apply, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs, neg_div]
  unfold vertInt Err
  dsimp [c, z, K] at hint hG
  simp_rw [← hint]
  rw [← (hind.sub hG).tsum_eq]
  grw [tsum_of_norm_bounded hSs.hasSum fun n => by
      rw [← mul_sub, norm_mul]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0]
      rw [norm_sub_rev]
      grw [ha n, perron_kernel_single_term (div_pos hu0 (mpr cast_pos (pos_of_ne_zero hn))) hc1.le (by linarith), mul_assoc],
    hSle, hTT']
  have := one_le_N N
  gcongr <;> nlinarith [show u ≤ N * u by nlinarith, log_nonneg (by linarith : 1 ≤ u)]

section
variable (hpx : IsPrimitive χ)
include hpx

theorem truncChange :
    ‖zsum χ T' u - zsum χ T u‖ ≤ 792 * Err N u T := by
  have hF' := zerosFinite χ T'
  have hF := zerosFinite χ T
  have := one_le_N N
  set D := toFinset hF' \ toFinset hF
  have hD ρ (hrx : ρ ∈ D) : 0 < re ρ ∧ re ρ < 1 ∧ T ≤ |im ρ| ∧ |im ρ| ≤ T + 1 ∧ LFunction χ ρ = 0 := by
    simp [D, ZerosBelow] at hrx
    grind
  unfold zsum Err
  rw [finsum_mem_eq_finite_toFinset_sum _ hF', finsum_mem_eq_finite_toFinset_sum _ hF,
    ← sum_sdiff (show toFinset hF ⊆ toFinset hF' from fun ρ hrx => by simp [ZerosBelow] at hrx ⊢
                                                                      grind), add_sub_cancel_right]
  have hsm := sum_mult_le hpx (T := T) D fun ρ hrx => by
    obtain ⟨a, b, c, d, e⟩ := hD ρ hrx
    exact mem_window a b e (by grind)
  have : 4 ≤ u * T := by nlinarith
  set L := log (N * u * T)
  have : 0.69 ≤ L := half_le_log
  have hLle := log_le_2log (show rN N * (T + 3) ≤ (N * u * T) ^ 2 by
    nlinarith [show rN N ≤ rN N ^ 2 by nlinarith, show T + 3 ≤ (u * T) ^ 2 by nlinarith, sq_nonneg (u * T)])
  have : 0 ≤ u / T := div_nonneg (by linarith) (by linarith)
  grw [norm_sum_le, sum_le_sum (g := fun ρ => mR χ ρ * (u / T)) fun ρ hrx => by
      obtain ⟨_, b, c, _, _⟩ := hD ρ hrx
      rw [norm_mul, norm_div, norm_natCast, norm_cpow_eq_rpow_re_of_pos (by linarith)]
      grw [trans_eq (rpow_le_rpow_of_exponent_le (by linarith) b.le) (rpow_one u), ← le_trans c (abs_im_le_norm ρ)]
      linarith,
    ← sum_mul, hsm, hLle]
  field_simp
  nlinarith [log_nonneg (by nlinarith : 1 ≤ rN N * u), show 0 ≤ u * L by nlinarith]

section
variable (hgood : GoodHeight χ T')
include hgood

abbrev riR f u T' := rectInt f (-0.5) (cLine u) (-T') T'

omit hT'1 in
lemma shiftResidue :
    ‖riR (fun s => ldL χ s * (cR u ^ s / s)) u T' / τI
      - (zsum χ T' u + eps0 χ * log u - del1 χ * (u - 1))‖ ≤ 6400 * log (2 * N) + S1 χ := by
  have hu2 := le_trans hT hTu
  have hc := one_lt_cLine hu2
  have hfin := zerosFinite χ T'
  set S := toFinset hfin
  let B := rectBdry (-0.5) (cLine u) (-T') T'
  let K := rect (-0.5) (cLine u) (-T') T'
  let O := rectOpen (-0.5) (cLine u) (-T') T'
  have hNO {ρ} (h1 : 0 < re ρ) (h2 : re ρ < 1) (h3 : LFunction χ ρ = 0) (heq : |im ρ| = T') : False := by
    have := log_pos (by nlinarith [one_le_N N] : 1 < rN N * T')
    exact not_lt_of_ge (by simpa [heq] using hgood ρ h1 h2 h3) (by positivity)
  have h0 : 0 ∈ O := by
    simp [O, rectOpen]
    grind
  have h1 : 1 ∈ O := by
    simp [O, rectOpen]
    grind
  have h0K := mem_of_mem_nhds (closed_nhds h0)
  obtain ⟨Z, g, hZ, hg, hg0, hfac⟩ := extract_zeros_Lent χ (isCompact_Icc.reProdIm isCompact_Icc)
    (by convert (((convex_Icc _ _).prod (convex_Icc _ _)).linear_preimage equivRealProdLm.toLinearMap).isPreconnected
        rfl)
    ⟨0, h0K, 1, mem_of_mem_nhds (closed_nhds h1), zero_ne_one⟩
  have hZeq : Z.erase 0 = S := by
    ext s
    simp [hZ, S]
    constructor
    · rintro ⟨hs0, ⟨⟨hx0, _⟩, hy⟩, hz⟩
      have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ hz)
      have hL := mp (Lent_eq_zero_iff hs1) hz
      have ⟨a, b⟩ := zeroStrip hpx hx0 hs0 hs1 hL
      exact ⟨a, b, lt_of_le_of_ne (mpr abs_le hy) (hNO a b hL), hL⟩
    · rintro ⟨a, b, c, d⟩
      exact ⟨by grind [zero_re], ⟨⟨by linarith, by linarith⟩, mp abs_le c.le⟩, mpr (Lent_eq_zero_iff (by grind [one_re])) d⟩
  have hZsum {s} : ∑ ρ ∈ Z, mC χ ρ / (s - ρ) = (∑ ρ ∈ S, mC χ ρ / (s - ρ)) + eps0 χ / s := by
    by_cases he : χ.Even ∧ χ ≠ 1
    · have h0Z : (0 : ℂ) ∈ Z := mpr (hZ 0) ⟨h0K, mpr (Lent_eq_zero_iff zero_ne_one) (mpr (L0_iff hpx) he)⟩
      rw [← add_sum_erase _ _ h0Z, hZeq, add_comm]
      simp [mC, mult, (mult_zero_of_even hpx he.1 he.2).2, eps0, he]
    · rw [← erase_eq_of_notMem (a := 0) fun h => he (mp (L0_iff hpx) (mp (Lent_eq_zero_iff zero_ne_one) (mp (hZ 0) h).2)), hZeq]
      simp [eps0, he]
  let H := logDeriv g
  have hHd : DifferentiableOn ℂ H K := fun s hs => ((hg s hs).deriv.differentiableAt.div (hg s hs).differentiableAt (hg0 s hs)).differentiableWithinAt
  have hHeq {s} (hs : s ∈ K) (hL0 : LFunction χ s ≠ 0) (hs1 : s ≠ 1) :
      ldL χ s = H s + (∑ ρ ∈ S, mC χ ρ / (s - ρ)) + eps0 χ / s - del1 χ / (s - 1) := by
    rw [logDeriv_Lent hs1 hL0, logDeriv_prod_factor (hfac s hs)
      (fun ρ hrx e => hL0 (mp (Lent_eq_zero_iff hs1) (mp sub_eq_zero e ▸ (mp (hZ ρ) hrx).2))) (hg0 s hs) (hg s hs).differentiableAt, hZsum]
    ring
  let E (s : ℂ) := cR u ^ s
  have hd s : HasDerivAt E (E s * cl u) s := (hasStrictDerivAt_const_cpow (inl (mpr ofReal_ne_zero (by linarith)))).hasDerivAt
  have hE : DifferentiableOn ℂ E K := fun s _ => (hd s).differentiableAt.differentiableWithinAt
  have hdE := mpr (differentiableOn_dslope (closed_nhds h0)) hE
  have hc_div {p} (hp : p ∈ O) {q} (hq : DifferentiableOn ℂ q K) : ContinuousOn (fun s => q s / (s - p)) B :=
    (hq.continuousOn.mono bdry_sub).div (by fun_prop) fun _ hs => sub_ne_zero_of_ne (bdry_ne hs hp)
  have hSmem ρ (hrx : ρ ∈ S) : ρ ≠ 0 ∧ ρ ∈ O := by
    obtain ⟨a, b, him, -⟩ := mp (mem_toFinset hfin) hrx
    exact ⟨by grind [zero_re], by simp [O, rectOpen]
                                  grind⟩
  have hc' : ContinuousOn (fun s => inv (s ^ 2)) B := ContinuousOn.inv₀ (by fun_prop) fun _ hs => pow_ne_zero 2 (bdry_ne hs h0)
  have hi0 : riR (fun s => inv (s ^ 2)) u T' = 0 := by
    have hd' {s} (hs : s ∈ B) : HasDerivAt (fun s => -inv s) (inv (s ^ 2)) s := by simpa [Pi.neg_def] using (hasDerivAt_inv (bdry_ne hs h0)).neg
    have hH {y} (hy : y = -T' ∨ y = T') := seg (d := 1) (hdH y) (fun _ hx => hd' (bdryH hx hy)) hc' fun _ hx => bdryH hx hy
    have hV {x} (hx : x = -0.5 ∨ x = cLine u) := seg (hdV x) (fun _ hy => hd' (bdryV hy hx)) hc' fun _ hy => bdryV hy hx
    simp only [one_smul] at hH
    simp only [rectInt, hH (inl rfl), hH (inr rfl), hV (inr rfl), hV (inl rfl)]
    ring
  let c0 : ℂ := ∑ ρ ∈ S, mC χ ρ / ρ
  let G s := H s * E s + (del1 χ - c0) * E s + eps0 χ * dslope E 0 s
  let q ρ s := mC χ ρ * (E s / ρ) / (s - ρ)
  have hG : DifferentiableOn ℂ G K := ((hHd.mul hE).add (hE.const_mul _)).add (hdE.const_mul _)
  have hEd ρ := (hE.div_const ρ).const_mul (mC χ ρ)
  have hEdc ρ (hrx : ρ ∈ S) := hc_div (hSmem ρ hrx).2 (hEd ρ)
  have hcG := hc_div h0 hG
  have hsc := continuousOn_finsetSum S hEdc
  have hc2 := hc'.const_mul (eps0 χ)
  have hc1 := hc_div h1 (hE.const_mul (-del1 χ))
  have hsumS {W} (hW : W ⊆ S) : riR (fun s => ∑ ρ ∈ W, q ρ s) u T' = ∑ ρ ∈ W, τI * (mC χ ρ * (E ρ / ρ)) := by
    induction W using Finset.induction with
    | empty => simp [rectInt]
    | insert a U ha ih =>
      obtain ⟨haS, hU⟩ := mp Finset.insert_subset_iff hW
      simpa [q, sum_insert ha, rectInt_div_sub (hSmem a haS).2 (hEd a), ih hU] using
        rectInt_add (hEdc a haS) (continuousOn_finsetSum U fun ρ h => hEdc ρ (hU h))
  have hcid : riR (fun s => ldL χ s * (cR u ^ s / s)) u T' =
      τI * (H 0 + zsum χ T' u - c0 + eps0 χ * log u - del1 χ * (u - 1)) := by
    rw [riR, rectInt_congr (g := fun s => (G s / (s - 0) + ∑ ρ ∈ S, q ρ s) + (eps0 χ * inv (s ^ 2) + -del1 χ * E s / (s - 1))) fun s hsb => by
          have hs := (bdry_sub : B ⊆ K) hsb
          have hs0 := bdry_ne hsb h0
          have hs1 := bdry_ne hsb h1
          have hL : LFunction χ s ≠ 0 := fun h0' => by
            have ⟨a, b⟩ := zeroStrip hpx hs.1.1 hs0 hs1 h0'
            rcases hsb with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> exact hNO a b h0' (by grind)
          dsimp [G]
          rw [hHeq hs hL hs1, dslope_of_ne _ hs0, slope_def_field, sub_zero]
          have hS : (∑ ρ ∈ S, mC χ ρ / (s - ρ)) * (E s / s) = (∑ ρ ∈ S, q ρ s) - c0 * E s / s := by
            simp only [c0, q, sum_mul, sum_div, ← sum_sub_distrib]
            exact sum_congr rfl fun ρ hrx => by field [(hSmem ρ hrx).1, sub_ne_zero_of_ne (bdry_ne hsb (hSmem ρ hrx).2)]
          rw [sub_mul, add_mul, add_mul, hS, show E 0 = 1 by simp [E]]
          field [sub_ne_zero_of_ne hs1],
      rectInt_add, rectInt_add, rectInt_add]
    · dsimp only [riR] at hsumS hi0
      rw [rectInt_div_sub h0 hG, hsumS subset_rfl, ← mul_sum, rectInt_const_mul, hi0, rectInt_div_sub h1 (hE.const_mul _),
        ofReal_log (by linarith), zsum, finsum_mem_eq_finite_toFinset_sum _ hfin]
      simp [G, c0, dslope_same, (hd 0).deriv, E]
      ring1
    exacts [hc2, hc1, hcG, hsc, hcG.add hsc, hc2.add hc1]
  obtain ⟨hZ0, hZ0sum⟩ := zerosWindow hpx 0
  let Zs := toFinset hZ0
  have hZsS : Zs ⊆ S := fun ρ hrx => by
    simp [Zs, S, ZerosNear, ZerosBelow] at hrx ⊢
    grind
  have hLN0 : LN N 0 = log (2 * N) := by simp [LN, mul_comm]
  let F z := H z + ∑ ρ ∈ S \ Zs, mC χ ρ / (z - ρ)
  have hFc : ContinuousAt F 0 := (hHd.continuousOn.continuousAt (closed_nhds h0)).add
    (tendsto_finsetSum (S \ Zs) fun ρ hrx => continuousAt_const.div (by fun_prop) (by simp [(hSmem ρ (sdiff_subset hrx)).1]))
  have hofR : Tendsto cR (𝓝[>] 0) (𝓝 0) := by simpa using (continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hmain := le_of_tendsto (hFc.norm.tendsto.comp hofR) (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 0.5), hofR.eventually_mem (closed_nhds h0),
      hofR.eventually_mem (hZ0.isClosed.isOpen_compl.mem_nhds fun h => by simpa using h.1)] with e ⟨he0, he1x⟩ hre heZ
    have hLe : LFunction χ e ≠ 0 := fun h => heZ ⟨by simpa using he0, by simp
                                                                         linarith, by simp, h⟩
    have he1p : cR e ≠ 1 := by
      simp
      linarith
    have hloc := localLemma hpx (s := e) (by simp
                                             linarith) (by simp
                                                           linarith) hLe he1p
    simp at hloc
    dsimp [F]
    convert hloc using 2
    rw [hHeq hre hLe he1p, finsum_mem_eq_finite_toFinset_sum _ hZ0, ← sum_sdiff hZsS]
    dsimp [Zs, cR]
    ring1)
  have hB1 : ZerosBelow χ 1 ⊆ ZerosNear χ 0 := fun ρ ⟨h1', h2, h3, h4⟩ => ⟨h1', h2, by simpa using h3.le, h4⟩
  have hB1f := hZ0.subset hB1
  have hQ0 : ‖∑ ρ ∈ Zs, mC χ ρ / ρ‖ ≤ S1 χ + 132 * log (2 * N) := by
    grw [norm_sum_le]
    simp [Zs]
    rw [← sum_sdiff (toFinset_mono (hs := hB1f) hB1), ← finsum_mem_eq_finite_toFinset_sum _ hB1f, add_comm]
    grw [sum_le_sum (g := mR χ) fun ρ hrx => by
      simp [ZerosBelow, ZerosNear] at hrx
      exact div_le_self (cast_nonneg _) (by grind [abs_im_le_norm ρ]),
      sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => cast_nonneg _,
      ← finsum_mem_eq_finite_toFinset_sum _ hZ0, hZ0sum, hLN0]
    rfl
  rw [hLN0] at hmain
  grw [nadd2 hmain (nneg hQ0) (by
    rw [hcid]
    dsimp [τI, F, c0]
    rw [← sum_sdiff hZsS]
    simp [div_neg, sum_neg_distrib]
    field_simp [pi_ne_zero]
    ring1)]
  linarith [hLN0 ▸ half_le_LN N 0]

theorem shiftBound :
    ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ ≤ 10100000 * Err N u T + S1 χ := by
  have := one_le_N N
  have hu2 := le_trans hT hTu
  have hu0 : 0 < u := by linarith
  have hT'0 : 0 ≤ T' := by linarith
  have : 0 < T' := by linarith
  have hc1 := one_lt_cLine hu2
  have := cLine_le_three hu2
  let f s := ldL χ s * (cR u ^ s / s)
  set L := log (N * u * T)
  set LT2 := log (N * (T' + 2))
  have : 2 ≤ rN N * u := by nlinarith
  have : 0 ≤ L := log_nonneg (by nlinarith)
  have : 0 ≤ LT2 := log_nonneg (by nlinarith)
  have hY2 : rN N * (4 * T ^ 2) ≤ (N * u * T) ^ 2 := by
    nlinarith [show rN N * 4 ≤ (rN N * u) ^ 2 by nlinarith, sq_nonneg T]
  have hf4 : LT2 ≤ 2 * L := log_le_2log (le_trans (by gcongr
                                                      nlinarith) hY2)
  have hhor h (hh : abs h = T') :
      ‖∫ x in -0.5..cLine u, f (cpx x h)‖ ≤ 4800000 * L ^ 2 * u / T := by
    grw [norm_integral_le_of_norm_le_const (C := 1350000 * L ^ 2 * u / T) fun x hx => by
      rw [uIoc_of_le (by linarith)] at hx
      simp only [f, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hu0]
      have hNT' := half_le_log (x := rN N * T')
      have hzn0 : T' ≤ ‖cpx x h‖ := by simpa [hh] using abs_im_le_norm (cpx x h)
      have : T' ≤ ‖cpx x h - 1‖ := by simpa [hh] using abs_im_le_norm (cpx x h - 1)
      have hkey := norm_logDeriv_le hpx (s := cpx x h) (by simp
                                                           linarith [hx.1]) (by simp
                                                                                linarith [hx.2])
        (by linarith) (by linarith)
        (mpr inv_pos (by linarith)) fun ρ ⟨a, b, _, d⟩ =>
          le_trans (hgood ρ a b d) (by have := abs_im_le_norm (cpx x h - ρ)
                                       simp at this
                                       grind)
      rw [div_inv_eq_mul] at hkey
      simp [LN, hh] at hkey
      grw [show ‖ldL χ (cpx x h)‖ ≤ 450000 * L ^ 2 by
          nlinarith [hkey, hf4, hNT', log_le_log (by nlinarith) (by nlinarith : rN N * T' ≤ rN N * u * T)],
        rpow_le_rpow_of_exponent_le (by linarith) (by simpa using hx.2), rpow_cLine hu2, exp_one_lt_three.le, ← hzn0, ← hTT']
      exact le_of_eq (by ring1)]
    rw [abs_of_nonneg (by linarith)]
    field_simp
    nlinarith [sq_nonneg L]
  have hf5 : arsinh T' ≤ 2 * L := le_trans arsinh_le_log (log_le_2log (le_trans (by nlinarith) hY2))
  have hleft := norm_int_inv_sqrt (f := fun t => f (cpx (-0.5) t)) (C := 13000 * LT2) hT'0 fun t ⟨ht1, ht2⟩ => by
    simp only [f, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hu0]
    have hkey := norm_logDeriv_le hpx (s := cpx (-0.5) t) (by simp) (by simp
                                                                        norm_num)
      (by grw [← abs_re_le_norm _]
          simp
          norm_num) (by grw [← abs_re_le_norm _]
                        simp
                        norm_num)
      (d := 0.5) (by norm_num) fun ρ hrx => by
        have := abs_re_le_norm (cpx (-0.5) t - ρ)
        simp at this
        grind [hrx.1]
    simp at hkey ⊢
    grw [hkey, show LN N t ≤ LT2 by dsimp [LN, LT2]
                                    gcongr
                                    linarith [mpr abs_le ⟨ht1.le, ht2⟩],
      rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num),
      ← show √(1 + t ^ 2) / 2 ≤ ‖cpx (-0.5) t‖ by
        rw [norm_add_mul_I, ← sqrt_sq zero_le_two, ← sqrt_div (by positivity)]
        gcongr
        nlinarith]
    field_simp
    linarith
  have hdiv : ‖(riR f u T' + τI * vertInt χ u T') / τI‖ ≤ 10000000 * Err N u T := by
    simp [τI]
    grw [div_le_self (norm_nonneg _) (by linarith [pi_gt_three]),
      nadd3 (hhor (-T') (by simp [hT'0])) (nneg (hhor T' (by simp [hT'0])))
        (by simpa using hleft : ‖-(I * _)‖ ≤ _) (by
          simp [rectInt, vertInt, f, neg_mul, integral_neg]
          field_simp [pi_ne_zero]
          ring1)]
    unfold Err
    grw [hf5, hf4]
    dsimp [L]
    field_simp
    nlinarith [log_nonneg (by nlinarith : 1 ≤ rN N * u), mul_le_mul_of_nonneg_right hTu (sq_nonneg (log (N * u * T)))]
  grw [nadd3 (nadd2 hdiv (nneg (shiftResidue hT hTu hTT' hpx hgood)) rfl)
    (show ‖-(eps0 χ * log u)‖ ≤ log u by
      grw [norm_neg, norm_mul, norm_eps0]
      simp [abs_of_nonneg (log_nonneg (by linarith : 1 ≤ u))])
    (nneg (norm_del1 (χ := χ)))
    (by dsimp [f, τI]
        field_simp [pi_ne_zero]
        ring1)]
  unfold Err
  linarith [half_le_log (x := rN N * u), show 0 ≤ u * log (N * u * T) ^ 2 / T by positivity,
    log_le_log (by linarith) (by nlinarith : u ≤ N * u), log_le_log (by positivity) (by nlinarith : 2 * rN N ≤ N * u)]
end
end
end SidesSec

end EF

open Complex EF

namespace AlpogeRHCore3

open Classical in
theorem explicitFormula :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
        ∀ u T : ℝ, 2 ≤ T → T ≤ u →
          ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}).Finite ∧
          ‖((∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
              (if χ = 1 then (u : ℂ) else 0)) +
            ∑ᶠ ρ ∈ ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}),
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
            C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
              ∑ᶠ ρ ∈ ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0}),
                (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖) := by
  refine ⟨10102292, by norm_num, fun N _ χ hpx u T hT hTu => ⟨zerosFinite χ T, ?_⟩⟩
  obtain ⟨T', hT1, hT2, hg⟩ := goodHeightExists hpx hT
  have : 0 ≤ S1 χ := finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  change ‖psiRaw χ u - (if χ = 1 then (u : ℂ) else 0) + zsum χ T u‖ ≤ _ * (Err N u T + S1 χ)
  grw [nadd3 (perronL hT hTu hT1 hT2) (shiftBound hT hTu hT1 hT2 hpx hg) (nneg (truncChange hT hTu hT1 hT2 hpx))
    (by unfold del1
        split_ifs <;> ring1)]
  linarith

end AlpogeRHCore3
