import Mathlib

noncomputable section

open Real hiding dist_eq
open Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul
open Topology Metric DirichletCharacter LSeries ZetaAsymptotics Asymptotics
open MeasureTheory hiding norm_integral_le_of_norm_le_const
open _root_.Filter hiding map_map mem_map
open ArithmeticFunction hiding ext log
open Inv
open MulChar hiding mul_apply coe_mk ext inv
open Finset hiding card_map mem_map ext map_cons sum_cons map_map mem_cons
open Set hiding Icc Ioc range ext mem_Icc
open Multiset hiding Icc Ioc coe_mk ext range mem_Icc
open Or (inl inr resolve_left)
open Eq (symm)
open Iff (mp mpr)
open LE.le (trans_eq)
open NeZero (pos ne)
open Option (elim elim_none elim_some eq_none_iff_forall_ne_some)
open Filter.Eventually (of_forall)
open ZMod (isUnit_iff_coprime)
open Nat (cast_nonneg cast_pos cast_one cast_pow cast_ne_zero cast_le floor_le floor_mono lt_floor_add_one prime_of_mem_primeFactors one_le_iff_ne_zero factorial_ne_zero)
open intervalIntegral (integral_eq_sub_of_hasDerivAt integral_of_le norm_integral_le_of_norm_le_const integral_congr integral_add)
open scoped Classical Real

abbrev a1 := @And.left
abbrev a2 := @And.right
abbrev clog := Complex.log

abbrev cR (x : ℝ) : ℂ := x
abbrev rN (n : ℕ) : ℝ := n
abbrev cN (n : ℕ) : ℂ := n
abbrev r0 : ℝ := 0
abbrev r1 : ℝ := 1
abbrev mkC (x y : ℝ) : ℂ := x + y * I

@[simp] lemma mkC_re (x y : ℝ) : re (mkC x y) = x := by simp [mkC]

lemma norm_cR_nn {x : ℝ} (hx : 0 ≤ x := by positivity) : ‖cR x‖ = x := by
  rw [norm_real, norm_of_nonneg hx]

def rectInt (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x in x0..x1, g (mkC x y0)) - (∫ x in x0..x1, g (mkC x y1)) +
    I * (∫ y in y0..y1, g (mkC x1 y)) - I * (∫ y in y0..y1, g (mkC x0 y))

lemma mellin_strip {f : ℂ → ℂ} {g : ℝ → ℂ} {A C : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hf : Differentiable ℂ f)
    (hgm : Measurable g) (hgb : ∀ x, ‖g x‖ ≤ C)
    (heq : ∀ {z}, 1 < re z → f z = z * ∫ x in Ioi A, cR x ^ (-z - 1) * g x)
    {s} (hs : 0 < re s) : ‖f s‖ ≤ C * (norm s / re s) * A ^ (-re s) := by
  have hA0 : 0 < A := by linarith
  let F := indicator (Ioi A) g
  have hFb x : ‖F x‖ ≤ C := le_trans (norm_indicator_le_norm_self _ _) $ hgb x
  have hme z : mellin F (-z) = ∫ x in Ioi A, cR x ^ (-z - 1) * g x := by
    rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi, mpr inter_eq_right $ Ioi_subset_Ioi hA0.le]
    simp [smul_eq_mul]
  have hfs : f s = s * mellin F (-s) := (hf.differentiableOn.analyticOnNhd $ isOpen_re_gt 0).eqOn_of_preconnected_of_eventuallyEq
    ((DifferentiableOn.analyticOnNhd (f := fun z => z * mellin F (-z)) fun z hz => by
      have := mellin_differentiableAt_of_isBigO_rpow (f := F) (s := -z) (a := 0)
        ((locallyIntegrableOn_const C).mono (hgm.indicator measurableSet_Ioi).aestronglyMeasurable $
          of_forall fun x => by simpa [norm_of_nonneg hC] using hFb x)
        (IsBigO.of_bound C $ of_forall fun x => by simpa using hFb x) (by simpa using hz)
        (IsBigO.of_bound 0 $ by
          filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
          simp [F, mpr not_lt $ show x ≤ A by linarith [a2 hx]]) (sub_one_lt _)
      fun_prop) $ isOpen_re_gt 0)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num)
    (Filter.Eventually.mono ((isOpen_re_gt 1).mem_nhds $ by norm_num) fun z hz => by simp [heq hz, hme]) hs
  rw [hfs, hme, norm_mul]
  grw [norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by linarith : -re s - 1 < -1) hA0).const_mul C) $ by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      grw [norm_mul, hgb x, norm_cpow_eq_rpow_re_of_pos $ lt_trans hA0 hx]
      simp [mul_comm],
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hA0]
  simp [show -re s - 1 + 1 = -re s by ring]
  ring_nf
  rfl

lemma zeta1_growth_half {s : ℂ} (hs : 0.5 ≤ re s) : ‖riemannZeta₁ s‖ ≤ 7 * (‖s‖ + 1) ^ 2 := by
  have hs' : 0 < re s := by positivity
  have hfb x : ‖ofReal $ Int.fract x‖ ≤ 1 := by
    simp
    grind [Int.abs_fract, Int.fract_lt_one]
  have h0 := mellin_strip (f := fun z => 1 - riemannZeta₀ z) le_rfl zero_le_one
    ((differentiable_const 1).sub differentiable_riemannZeta₀) (by measurability) hfb (fun {z} hz => by
      have h := LSeries_one_eq_riemannZeta hz ▸ LSeries_eq_mul_integral' 1 zero_le_one hz $ by simp
                                                                                               rfl
      simp at h
      rw [(setIntegral_congr_fun measurableSet_Ioi fun x hx => by
            have hx0 := lt_trans zero_lt_one hx.out
            have := mpr ofReal_ne_zero hx0.ne'
            simp [Int.fract, ← Int.natCast_floor_eq_floor hx0.le, neg_add_eq_sub, cpow_sub _ _ this]
            field).trans $ integral_sub (integrableOn_Ioi_cpow_of_lt (a := -z) (by simpa) zero_lt_one) $
          (integrableOn_Ioi_cpow_of_lt (a := -z - 1) (by simp; linarith) zero_lt_one).mul_bdd
            (by measurability) $ of_forall hfb,
        integral_Ioi_cpow_of_lt (by simpa) zero_lt_one] at h
      simp [mul_comm] at *
      grind [riemannZeta₀, one_re]) hs'
  simp [one_rpow, mul_one] at h0
  have : ‖s‖ / re s ≤ 2 * ‖s‖ := mpr (div_le_iff₀ hs') $ by norm_num at hs
                                                            nlinarith [norm_nonneg s]
  rw [riemannZeta₁, show riemannZeta₀ s = 1 - (1 - riemannZeta₀ s) by ring]
  grw [norm_add_le, norm_mul, norm_sub_le, norm_sub_le, h0, this]
  norm_num
  nlinarith [norm_nonneg s]

theorem l_function_partial_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hx_ : χ ≠ 1)
    (s : ℂ) (hs : 0 < re s) (N : ℕ) (hN : 1 ≤ N) :
    ‖LFunction χ s - ∑ n ∈ Icc 1 N, χ (n : ZMod q) * cN n ^ (-s)‖ ≤
      2 * rN q * (norm s / re s) * rN N ^ (-re s) := by
  have hN1 : r1 ≤ N := by exact_mod_cast hN
  let Ap n : ℂ := ∑ k ∈ range n, χ k
  have hzero : Ap q = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero $ ne q
    dsimp [Ap]
    rw [← Fin.sum_univ_eq_sum_range, ← sum_eq_zero_of_ne_one hx_]
    exact sum_congr rfl fun (i : ZMod $ m + 1) _ => congrArg χ $ ZMod.natCast_zmod_val i
  have hB K : ‖Ap K‖ ≤ q := by
    induction K using Nat.strong_induction_on with | _ K ih =>
      by_cases hK : K < q
      grw [norm_sum_le, sum_le_sum fun _ _ => norm_le_one χ _]
      simpa using hK.le
      rw [show Ap K = Ap (K - q) by rw [← Nat.add_sub_of_le $ mp not_lt hK]; simp [Ap, sum_range_add, hzero]]
      exact ih _ $ by have := pos q
                      omega
  let g k : ℂ := if k ≤ N then 0 else χ k
  let S m := ∑ k ∈ Icc 1 m, g k
  have hSeq m : S m = if m ≤ N then 0 else Ap (m + 1) - Ap (N + 1) := by
    induction m with
    | zero => simp [S]
    | succ m ih =>
      rw [show S (m + 1) = S m + g (m + 1) by simp [S, sum_Icc_succ_top], ih]
      split_ifs <;> grind [sum_range_succ]
  have hSb m : ‖S m‖ ≤ 2 * q := by
    rw [hSeq]
    split_ifs
    simp
    linarith [norm_sub_le (Ap $ m + 1) $ Ap $ N + 1, hB $ m + 1, hB $ N + 1]
  exact mellin_strip (f := fun z => LFunction χ z - ∑ n ∈ Icc 1 N, χ n * cN n ^ (-z)) hN1 (by positivity)
    ((differentiable_LFunction hx_).fun_sub $ Differentiable.fun_sum (u := Icc 1 N)
      (A := fun n z => χ n * n ^ (-z)) fun n hn => by
        fun_prop (disch := left; exact (mpr cast_ne_zero $ by rw [mem_Icc] at hn; omega)))
    ((measurable_from_top (f := S)).comp Nat.measurable_floor) (fun x => hSb ⌊x⌋₊) (fun {z} hz => by
      have hSg : LSeriesSummable g z :=
        Summable.of_norm_bounded (LSeriesSummable_of_one_lt_re χ hz).norm fun n => by
          simp [norm_term_eq, g]
          split_ifs <;> simp
          positivity
      have hLg : LFunction χ z - ∑ n ∈ Icc 1 N, χ n * n ^ (-z) = LSeries g z := by
        rw [LFunction_eq_LSeries χ hz, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_comm,
          LSeries, LSeries, ← (LSeriesSummable_of_one_lt_re χ hz).tsum_sub hSg,
          tsum_eq_sum (s := Icc 1 N) fun n hn => by
            rw [term_def, term_def]
            simp [g]
            split_ifs <;> simp at *
            omega]
        refine sum_congr rfl fun n hn => ?_
        rw [mem_Icc] at hn
        simp [term_of_ne_zero $ show n ≠ 0 by omega, g, a2 hn, div_eq_mul_inv, cpow_neg]
      rw [hLg, LSeries_eq_mul_integral g le_rfl (by linarith) hSg $
        IsBigO.of_bound (2 * q) $ of_forall fun n => by simpa [S] using hSb n]
      congr 1
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hN1) fun x hx => by
        have : S ⌊x⌋₊ = 0 := by
          rw [hSeq]
          simp [Nat.floor_le_of_le $ mp not_lt $ by simpa using a2 hx]
        simp [S] at this
        simp [this]]
      exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp [S, mul_comm, neg_add_eq_sub]) hs

def Sa (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n * cR (1 - n / x)

theorem localZeroDslope {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c 0.5)) (hf0 : f c ≠ 0)
    (hbd : ∀ z ∈ closedBall c 0.5, ‖f z‖ ≤ ‖f c‖ * exp M) :
    ∃ Z : Multiset ℂ,
      (∀ rho : ℂ, rho ∈ Z ↔ rho ∈ closedBall c 0.13 ∧ f rho = 0) ∧
      (∀ rho ∈ Z, rho ∉ Z.erase rho ↔ deriv f rho ≠ 0) ∧
      (Z.card : ℝ) ≤ M ∧
      ∀ z ∈ closedBall c 0.08, f z ≠ 0 →
        ‖deriv f z / f z - (Z.map fun rho => inv (z - rho)).sum‖ ≤ 336 * (M + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  induction n generalizing f M
  all_goals
    have hM := hbd c $ mem_closedBall_self $ by norm_num
    simp [hf0] at hM
  simp at hn
  linarith
  next n ih =>
    by_cases hex : ∃ rho0 ∈ closedBall c 0.13, f rho0 = 0
    obtain ⟨rho0, hρ₀, hfρ₀⟩ := hex
    obtain ⟨g, hgd, rfl⟩ : ∃ g, DifferentiableOn ℂ g (closedBall c 0.5) ∧ (· - rho0) * g = f :=
      ⟨_, mpr (differentiableOn_dslope $ closedBall_mem_nhds_of_mem $ closedBall_subset_ball (by norm_num) hρ₀) hf,
        funext $ sub_smul_dslope_of_zero hfρ₀⟩
    simp at hf0
    have hgbd z (hz : z ∈ closedBall c 0.5) : ‖g z‖ ≤ ‖g c‖ * exp (M - 1) :=
      norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hgd.diffContOnCl_ball subset_rfl) (fun w hw => by
        rw [frontier_ball _ $ by norm_num, mem_sphere_iff_norm] at hw
        have h1 := hbd w $ by simp [dist_eq_norm, hw]
        have h2 := norm_sub_le_norm_sub_add_norm_sub w rho0 c
        have h3 := mp mem_closedBall_iff_norm hρ₀
        simp at h1
        rw [norm_sub_rev c, show exp M = exp (M - 1) * exp 1 by rw [← exp_add]; ring_nf] at h1
        grw [h3, le_of_lt exp_one_lt_d9] at h1
        nlinarith [norm_nonneg $ g w]) $ by rwa [closure_ball c $ by norm_num]
    obtain ⟨Z', hZ', hmult', hsum', hder'⟩ := ih hgd (a2 hf0) hgbd (by push_cast at hn
                                                                       linarith)
    have hdg u (hu : u ∈ closedBall c 0.13) := hgd.differentiableAt $ closedBall_mem_nhds_of_mem $ closedBall_subset_ball (by norm_num) hu
    have hmul_deriv rho (hr_ : rho ∈ closedBall c 0.13) : deriv ((· - rho0) * g) rho = g rho + (rho - rho0) * deriv g rho := by
      rw [deriv_mul (by fun_prop) $ hdg rho hr_]
      simp
    refine ⟨rho0 ::ₘ Z', fun rho => ?_, fun rho hr_ => ?_, by simp
                                                              linarith, fun z hz hfz => ?_⟩
    rw [mem_cons, hZ']
    simp only [Pi.mul_apply, mul_eq_zero, sub_eq_zero]
    rcases eq_or_ne rho rho0 with rfl | hne <;> [simp [hρ₀]; simp [hne]]
    rcases eq_or_ne rho rho0 with rfl | hne
    rw [erase_cons_head, hZ', hmul_deriv rho hρ₀]
    simp [hρ₀]
    have hrZ' := (mp mem_cons hr_).resolve_left hne
    obtain ⟨h1, h2⟩ := mp (hZ' rho) hrZ'
    rw [erase_cons_tail Z' hne.symm, mem_cons, not_or, hmult' rho hrZ', hmul_deriv rho h1, h2, zero_add]
    simp [hne, mpr sub_ne_zero hne]
    simp at hfz
    rw [← logDeriv_apply, logDeriv_mul z (a1 hfz) (a2 hfz) (by fun_prop) $ hdg z $ closedBall_subset_closedBall (by norm_num) hz,
      logDeriv_apply, logDeriv_apply, deriv_sub_const, deriv_id'', one_div, map_cons, sum_cons, add_sub_add_left_eq_sub]
    linarith [hder' z hz $ a2 hfz]
    refine ⟨0, fun rho => ⟨by simp, fun ⟨h, h0⟩ => (hex ⟨rho, h, h0⟩).elim⟩,
      by simp, by simpa, fun z hz _ => ?_⟩
    have hfb := hf.mono $ le_trans ball_subset_closedBall $ closedBall_subset_closedBall $ show (0.13 : ℝ) ≤ 0.5 by norm_num
    have hneb w (hw : w ∈ ball c 0.13) : f w ≠ 0 := fun h0 => hex ⟨w, ball_subset_closedBall hw, h0⟩
    obtain ⟨g, hg0, hgd⟩ := ((hfb.deriv isOpen_ball).div hfb hneb).isExactOn_ball.with_val_at c 0
    have hg_diff : DifferentiableOn ℂ g $ ball c 0.13 := fun u hu => (hgd u hu).differentiableAt.differentiableWithinAt
    obtain ⟨k, hk, hfg⟩ := mp (logDeriv_eqOn_iff hfb hg_diff.cexp isOpen_ball isPreconnected_ball (by simp) hneb)
      fun u hu => by simp [logDeriv_apply, (hgd u hu).cexp.deriv]
    have hsub : closedBall z 0.025 ⊆ ball c 0.13 := fun w hw => by
      simp [dist_eq_norm]
      linarith [mp mem_closedBall_iff_norm hz, mp mem_closedBall_iff_norm hw, norm_sub_le_norm_sub_add_norm_sub w z c]
    have hvc {v} (hv : v ∈ ball 0 0.13) : c + v ∈ ball c 0.13 := by simpa [mem_ball, dist_eq_norm] using hv
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 0.025) (C := 8.4 * (M + 1))
      (by norm_num) ((hg_diff.mono hsub).diffContOnCl_ball subset_rfl) fun w hw => by
        have : ‖w - c‖ ≤ 0.105 := by
          linarith [mp mem_closedBall_iff_norm hz, mp mem_sphere_iff_norm hw, norm_sub_le_norm_sub_add_norm_sub w z c]
        have hbc := borelCaratheodory_zero (f := fun v => g $ c + v) (z := w - c) (M := M + 1) (by linarith)
          (hg_diff.comp (differentiable_id.const_add c).differentiableOn fun _ => hvc)
          (fun v hv => by
            have h := hbd (c + v) $ closedBall_subset_closedBall (by norm_num) $ ball_subset_closedBall $ hvc hv
            simp [hfg $ hvc hv, hfg $ mem_ball_self $ by norm_num, hg0, norm_exp, mpr norm_pos_iff hk] at h
            dsimp
            linarith) (by norm_num) (mpr mem_ball_zero_iff $ by linarith) $ by simpa using hg0
        simp at hbc
        grw [hbc]
        rw [div_le_iff₀ $ by linarith]
        nlinarith
    simpa [(hgd z $ hsub $ mem_closedBall_self $ by norm_num).deriv] using trans_eq hder $ by ring

abbrev DC (q : ℕ) := DirichletCharacter ℂ q
abbrev lcond (q : ℕ) (t : ℝ) : ℝ := log (rN q * (abs t + 2))
abbrev slog (x : ℝ) : ℝ := sqrt (log x)
abbrev zterm (y β : ℝ) : ℂ := cR y ^ cR β / (cR β * (cR β + 1))

def InRegion (c : ℝ) (q : ℕ) (s : ℂ) : Prop := 1 - c / lcond q (im s) ≤ re s
abbrev partialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n
def Schi {q : ℕ} (χ : DC q) (y : ℝ) : ℂ := Sa (fun n => ↑(Λ n) * χ n) y

lemma one_le_modulus_real (q : ℕ) [NeZero q] : r1 ≤ q := by exact_mod_cast one_le_iff_ne_zero.2 (ne q)
lemma lcond_ge_const (q : ℕ) [NeZero q] (t : ℝ) : 0.69 ≤ lcond q t := by
  linarith [log_two_gt_d9, log_le_log two_pos (by nlinarith [one_le_modulus_real q, abs_nonneg t] : 2 ≤ rN q * (abs t + 2))]
lemma lcond_pos (q : ℕ) [NeZero q] (t : ℝ) : 0 < lcond q t := by linarith [lcond_ge_const q t]

section
variable {q : ℕ} [NeZero q]

abbrev L1 (χ : DC q) : ℂ → ℂ := if χ = 1 then riemannZeta₁ else LFunction χ
def IsLZero (χ : DC q) (s : ℂ) : Prop := (χ ≠ 1 ∨ s ≠ 1) ∧ LFunction χ s = 0
def ExcZeros (c1_ : ℝ) (χ : DC q) (bet0 : Option ℝ) : Prop :=
  (∀ β ∈ bet0, χ ≠ 1 ∧ 0.5 ≤ β ∧ β < 1 ∧ InRegion c1_ q (cR β) ∧ LFunction χ (cR β) = 0 ∧
    deriv (LFunction χ) (cR β) ≠ 0) ∧
  ∀ s : ℂ, InRegion c1_ q s → IsLZero χ s → ∃ β ∈ bet0, s = cR β
def negLD (χ : DC q) (s : ℂ) : ℂ := -(deriv (LFunction χ) s / LFunction χ s)
def Fchi (χ : DC q) (y : ℝ) (w : ℂ) : ℂ := negLD χ w * y ^ w / (w * (w + 1))

theorem lfunction_polynomial_growth (χ : DC q) (hx_ : χ ≠ 1)
    (s : ℂ) (hs : 0.5 ≤ re s) : ‖LFunction χ s‖ ≤ 5 * q * (1 + norm s) := by
  have hs' : 0 < re s := by positivity
  have hP := l_function_partial_sum χ hx_ s hs' 1 le_rfl
  simp only [cast_one, one_rpow, mul_one, Finset.Icc_self, Finset.sum_singleton, one_cpow] at hP
  have hdiv : norm s / re s ≤ 2 * norm s := mpr (div_le_iff₀ hs') (by norm_num at hs
                                                                      nlinarith [norm_nonneg s])
  have hL := le_trans (norm_le_insert' (LFunction χ s) (χ 1)) (add_le_add (norm_le_one χ _) hP)
  nlinarith [one_le_modulus_real q, norm_nonneg s, mul_le_mul_of_nonneg_left hdiv $ cast_nonneg (α := ℝ) q]

section
open scoped LSeries.notation

lemma negLD_eq_LSeries_mul_vonMangoldt (χ : DC q) {s : ℂ} (hs : 1 < re s) :
    negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [LSeries_twist_vonMangoldt_eq χ hs,
    deriv_LFunction_eq_deriv_LSeries χ hs,
    LFunction_eq_LSeries χ hs]
  ring

def ldB : ℝ := log_deriv_riemannZeta_add_inv_sub_bounded.bound.choose
def ldEps : ℝ := (mp mem_nhdsWithin_iff log_deriv_riemannZeta_add_inv_sub_bounded.bound.choose_spec).choose
def ldC : ℝ := max (max ldB 0) (re (L ↗Λ (cR (1 + ldEps / 2))))
lemma ldC_nonneg : 0 ≤ ldC := le_max_of_le_left (le_max_right _ _)

theorem l_log_deriv_right (χ : DC q) {s : ℂ} (hs : 1 < re s) :
    ‖negLD χ s‖ ≤ 1 / (re s - 1) + ldC := by
  obtain ⟨he_, hball⟩ := (mp mem_nhdsWithin_iff log_deriv_riemannZeta_add_inv_sub_bounded.bound.choose_spec).choose_spec
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs, one_div]
  have hmono {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ re s) : ‖L (↗χ * ↗Λ) s‖ ≤ re (L ↗Λ $ cR σ) :=
    tsum_of_norm_bounded (hasSum_re (LSeriesSummable_vonMangoldt $ by simpa using h1).hasSum) fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      simp
      rw [norm_term_eq, term_of_ne_zero hn, ← ofReal_natCast, ← ofReal_cpow $ cast_nonneg n, ← ofReal_div, ofReal_re]
      simp [hn, abs_of_nonneg vonMangoldt_nonneg]
      grw [norm_le_one χ _, rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_iff_ne_zero.2 hn) h2]
      simp
  rcases lt_or_ge (re s) $ 1 + ldEps / 2 with hlt | hge
  let sr := cR $ re s
  have := hmono hs le_rfl
  have hreal : ‖sr - 1‖ = re s - 1 := by rw [← ofReal_one, ← ofReal_sub, norm_cR_nn]
  have hb : ‖deriv riemannZeta sr / riemannZeta sr + inv (sr - 1)‖ ≤ ldB := by
    simpa [ldB] using hball ⟨by rw [mem_ball, dist_eq, hreal]
                                dsimp [ldEps] at hlt
                                linarith, by simp [sr, ne_of_gt hs]⟩
  have htri := norm_add_le (deriv riemannZeta sr / riemannZeta sr + inv (sr - 1)) (-inv (sr - 1))
  simp only [add_neg_cancel_right, norm_neg, norm_inv, hreal] at htri
  have := trans_eq (re_le_norm $ L ↗Λ sr) $ by rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div $ by simpa [sr] using hs, neg_div, norm_neg]
  linarith [show ldB ≤ ldC from le_max_of_le_left $ le_max_left _ _]
  have := hmono (by dsimp [ldEps]
                    linarith) hge
  dsimp [ldC]
  linarith [le_max_right (max ldB 0) $ re $ L ↗Λ $ cR $ 1 + ldEps / 2, show 0 ≤ inv (re s - 1) by positivity]

end

lemma lfunction_norm_near_one (χ : DC q) (hx_ : χ ≠ 1) {w : ℂ} {δ : ℝ}
    (hd : 0 ≤ δ) (hw : 1 - δ ≤ re w) (hw4 : 0.5 ≤ re w := by norm_num) (hw2 : norm w ≤ 2 := by norm_num) :
    ‖LFunction χ w‖ ≤ (9 + log q) * rN q ^ δ := by
  have hq := one_le_modulus_real q
  let S := ∑ n ∈ Icc 1 q, χ n * cN n ^ (-w)
  have h1 : norm S ≤ (1 + log q) * rN q ^ δ := by
    grw [norm_sum_le, sum_le_sum (g := fun n => rN q ^ δ * inv (rN n)) fun n hn => by
        obtain ⟨h1, h2⟩ := mp mem_Icc hn
        have hn0 : 0 < rN n := mpr cast_pos h1
        rw [norm_mul, norm_natCast_cpow_of_pos h1, neg_re,
          show rN n ^ (-re w) = rN n ^ (1 - re w) * inv (rN n) by
            rw [← rpow_neg_one, ← rpow_add hn0]
            congr 1
            ring]
        grw [norm_le_one χ _, rpow_le_rpow_of_exponent_le (by exact_mod_cast h1) $ show 1 - re w ≤ δ by linarith,
          rpow_le_rpow hn0.le (by exact_mod_cast h2 : rN n ≤ rN q) hd]
        simp,
      ← mul_sum, show ∑ n ∈ Icc 1 q, inv (rN n) = harmonic q by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl,
      harmonic_le_one_add_log q]
    exact le_of_eq $ mul_comm _ _
  have htail : ‖LFunction χ w - S‖ ≤ 8 * rN q ^ δ := by
    grw [l_function_partial_sum χ hx_ w (by linarith) q $ pos q,
      show norm w / re w ≤ 4 from mpr (div_le_iff₀ $ by linarith) $ by linarith]
    rw [show 2 * rN q * 4 * rN q ^ (-re w) = 8 * rN q ^ (1 - re w) by
      rw [sub_eq_add_neg, rpow_add $ by linarith, rpow_one]
      ring]
    grw [rpow_le_rpow_of_exponent_le hq $ show 1 - re w ≤ δ by linarith]
  linarith [le_trans (norm_le_insert' _ _) $ add_le_add h1 htail]

end

variable {q : ℕ} [NeZero q]

section
open scoped LSeries.notation

lemma negLD_341 {r : ℕ} [NeZero r] (χ : DC q) (ψ : DC r)
    (hψ : ∀ n : ℕ, IsUnit (n : ZMod q) → ψ n = χ n ^ 2) {σ : ℝ} (hs : 1 < σ) (t : ℝ) :
    0 ≤ 3 * re (negLD (1 : DC 1) σ) + 4 * re (negLD χ (mkC σ t)) + re (negLD ψ (mkC σ (2 * t))) := by
  have hS {m : ℕ} [NeZero m] (φ : DC m) u c :
      HasSum (fun n => c * re (term (↗φ * ↗Λ) (mkC σ u) n)) (c * re (negLD φ (mkC σ u))) := by
    rw [negLD_eq_LSeries_mul_vonMangoldt φ $ by simp [hs]]
    exact (hasSum_re (LSeriesSummable_twist_vonMangoldt φ $ by simp [hs]).hasSum).mul_left c
  simpa [mkC] using (((hS (1 : DC 1) 0 3).add $ hS χ t 4).add $ hS ψ (2 * t) 1).nonneg fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    simp
    have hre {m : ℕ} [NeZero m] (φ : DC m) u :
        re (term (↗φ * ↗Λ) (mkC σ u) n) = Λ n / n ^ σ * re (φ n / n ^ (u * I)) := by
      rw [mkC, term_of_ne_zero hn, cpow_add _ _ (mpr cast_ne_zero hn), ← re_ofReal_mul]
      congr 1
      push_cast
      rw [ofReal_cpow (cast_nonneg n)]
      simp [div_mul_div_comm]
      ring
    simp only [hre, mul_one, one_mul, ofReal_zero, zero_mul, cpow_zero, div_one, Subsingleton.elim (n : ZMod 1) 1, map_one, one_re]
    have : 0 ≤ Λ n / n ^ σ := by positivity
    have hcp u : ‖cN n ^ (cR u * I)‖ = 1 := by
      rw [norm_natCast_cpow_of_pos $ pos_of_ne_zero hn]
      simp
    by_cases hu : IsUnit (n : ZMod q)
    set w := χ n / cN n ^ (cR t * I) with hw
    have : re w ^ 2 + im w ^ 2 ≤ 1 := by
      rw [sq, sq, ← normSq_apply, normSq_eq_norm_sq]
      nlinarith [norm_nonneg w, show norm w ≤ 1 by simp [w, hcp, norm_le_one χ _]]
    rw [hψ n hu, show cR (2 * t) * I = cN 2 * (t * I) by push_cast; ring, cpow_nat_mul, ← div_pow, ← hw, sq, mul_re]
    nlinarith [sq_nonneg $ 1 + re w]
    rw [map_nonunit χ hu, zero_div, zero_re]
    nlinarith [a1 $ mp abs_le $ le_trans (abs_re_le_norm $ ψ n / cN n ^ (cR (2 * t) * I)) $ show ‖ψ n / cN n ^ (cR (2 * t) * I)‖ ≤ 1 by rw [norm_div, hcp, div_one]; exact norm_le_one ψ _]

end

lemma zeta1_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ $ mpr sub_ne_zero hs]

lemma L1_eq_zero_iff {χ : DC q} (hxq_ : χ ≠ 1 ∨ q = 1) {s : ℂ} :
    L1 χ s = 0 ↔ IsLZero χ s := by
  by_cases h1 : χ = 1
  obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
  subst h1
  simp [L1, IsLZero, ↓reduceIte]
  exact ⟨fun h => have hs1 : s ≠ 1 := fun hs => by simp [hs] at h
    ⟨hs1, by have := zeta1_eq hs1
             grind⟩, fun ⟨hs1, hz_⟩ => by rw [zeta1_eq hs1, hz_, mul_zero]⟩
  simp [L1, IsLZero, h1]

lemma L1_ne_zero_of_one_le_re {χ : DC q} (hxq_ : χ ≠ 1 ∨ q = 1)
    {s : ℂ} (hs : 1 ≤ re s) : L1 χ s ≠ 0 := fun h => by
  obtain ⟨hne, h0⟩ := mp (L1_eq_zero_iff hxq_) h
  exact LFunction_ne_zero_of_one_le_re χ hne hs h0

lemma L1_log_deriv {χ : DC q} (hxq_ : χ ≠ 1 ∨ q = 1)
    {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) (hL : L1 χ s ≠ 0) :
    deriv (L1 χ) s / L1 χ s = -negLD χ s + (if χ = 1 then 1 / (s - 1) else 0) := by
  by_cases h1 : χ = 1
  obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
  subst h1
  simp [negLD] at hL ⊢
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]
  simp [L1, negLD, h1]

section
open scoped LSeries.notation ArithmeticFunction.Moebius

lemma L1_local_expansion (χ : DC q) (hxq_ : χ ≠ 1 ∨ q = 1) (t : ℝ) :
    ∃ Z : Multiset ℂ,
      (∀ rho, rho ∈ Z ↔ rho ∈ closedBall (mkC 1.05 t) 0.13 ∧ L1 χ rho = 0) ∧
      (∀ rho ∈ Z, rho ∉ Z.erase rho ↔ deriv (L1 χ) rho ≠ 0) ∧
      rN Z.card ≤ 16 * lcond q t ∧
      (∀ z ∈ closedBall (mkC 1.05 t) 0.08, L1 χ z ≠ 0 →
        ‖deriv (L1 χ) z / L1 χ z - (Z.map fun rho => inv (z - rho)).sum‖ ≤ 5900 * lcond q t) ∧
      ∀ σ, 1 < σ → σ ≤ 1.1 →
        (∀ rho ∈ Z, 0 ≤ re (inv (mkC σ t - rho))) ∧
        re (negLD χ (mkC σ t)) ≤ (if χ = 1 then re (inv (mkC (σ - 1) t)) else 0) + 5900 * lcond q t - (Z.map fun rho => re (inv (mkC σ t - rho))).sum ∧
        re (negLD χ (mkC σ t)) ≤ (if χ = 1 then re (inv (mkC (σ - 1) t)) else 0) + 5900 * lcond q t := by
  let z0_ := mkC 1.05 t
  let T2 := abs t + 2
  have hz0re : re z0_ = 1.05 := by simp [z0_]
  have := one_le_modulus_real q
  have hqT : 2 ≤ q * T2 := by nlinarith [abs_nonneg t]
  have hlow : 1 ≤ 420 * ‖L1 χ z0_‖ := by
    have hs : 1 < re z0_ := by linarith
    have h21 : 1 ≤ 21 * ‖LFunction χ z0_‖ := by
      have hS1 := (mpr LSeriesSummable_one_iff hs).norm
      have haux := zeta_limit_aux1 hs
      have htnn : 0 ≤ termTSum (re z0_) := tsum_nonneg fun _ => term_nonneg _ _
      grw [← norm_one (α := ℂ), ← mul_mu_eq_one χ hs, ← LFunction_eq_LSeries χ hs, norm_mul, LSeries,
        tsum_of_norm_bounded hS1.hasSum fun n => norm_term_le _ $ by
          simp
          grw [norm_le_one χ _]
          simp
          exact_mod_cast abs_moebius_le_one]
      rw [hS1.tsum_eq_zero_add]
      simp_rw [norm_term_eq]
      simp [hz0re] at haux htnn ⊢
      nlinarith [norm_nonneg $ LFunction χ z0_]
    by_cases h1 : χ = 1
    obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
    have : 0.05 ≤ ‖z0_ - 1‖ := le_trans (by simp [z0_]; norm_num) $ re_le_norm _
    subst h1
    simp [L1] at h21 ⊢
    rw [zeta1_eq $ mp sub_ne_zero $ mp norm_pos_iff $ by linarith, norm_mul]
    nlinarith [norm_nonneg $ riemannZeta z0_]
    simp [L1, h1]
    nlinarith [norm_nonneg $ LFunction χ z0_]
  have hbound z (hz : z ∈ closedBall z0_ 0.5) : ‖L1 χ z‖ ≤ ‖L1 χ z0_‖ * exp (16 * lcond q t) := by
    have := mp mem_closedBall_iff_norm hz
    have hre : 0.5 ≤ re z := by
      linarith [a1 $ mp abs_le $ abs_re_le_norm $ z - z0_, show re (z - z0_) = re z - 1.05 by simp [z0_]]
    have hsq : (norm z + 1) ^ 2 ≤ 4 * T2 ^ 2 := by
      have : norm z0_ ≤ 1.05 + abs t := le_trans (norm_le_abs_re_add_abs_im z0_) $ by simp [z0_]
                                                                                      norm_num
      nlinarith [norm_sub_norm_le z z0_, norm_nonneg z, abs_nonneg t]
    have hLz : ‖L1 χ z‖ ≤ 7 * rN q * (norm z + 1) ^ 2 := by
      dsimp [L1]
      split_ifs with h1
      nlinarith [zeta1_growth_half hre]
      nlinarith [lfunction_polynomial_growth χ h1 z hre, show 1 + norm z ≤ (norm z + 1) ^ 2 by nlinarith [norm_nonneg z]]
    rw [show exp (16 * lcond q t) = (q * T2) ^ 16 by
      rw [show 16 * lcond q t = rN 16 * log (q * T2) by norm_num; rfl, exp_nat_mul, exp_log $ by positivity]]
    grw [hLz, hsq, show rN q ≤ rN q ^ 2 by nlinarith]
    have : 28 * (q * T2) ^ 2 ≤ (q * T2) ^ 16 / 420 := by
      nlinarith [pow_le_pow_left₀ zero_le_two hqT 14, show (q * T2) ^ 16 = (q * T2) ^ 14 * (q * T2) ^ 2 by ring, sq_nonneg $ q * T2]
    nlinarith [hlow, sq_nonneg $ q * T2]
  have hLdiff : Differentiable ℂ $ L1 χ := by
    dsimp [L1]
    split_ifs with h
    exacts [differentiable_riemannZeta₁, differentiable_LFunction h]
  obtain ⟨Z, hZ, hmult, hsum, hbd⟩ := localZeroDslope (f := L1 χ) (c := z0_) hLdiff.differentiableOn (fun h => by norm_num [h] at hlow) hbound
  have := lcond_ge_const q t
  refine ⟨Z, hZ, hmult, hsum, fun z hz hnz => by linarith [hbd z hz hnz], fun σ hs1_ hs2 => ?_⟩
  let w := mkC σ t
  have hwne := L1_ne_zero_of_one_le_re hxq_ (s := w) $ by simp [w, hs1_.le]
  have h1 := le_trans (trans_eq (re_le_norm $ -(deriv (L1 χ) w / L1 χ w - (Z.map fun rho => inv $ w - rho).sum)) $ norm_neg _)
    (hbd w (by
      rw [mem_closedBall, dist_eq_norm, show w - z0_ = cR (σ - 1.05) by simp [w, z0_], norm_real, norm_eq_abs, abs_le]
      grind) hwne)
  have hld := congrArg re $ L1_log_deriv hxq_ (inr fun h => by linarith [show σ = 1 by simpa [w] using congrArg re h]) hwne
  have hsum' : re ((Z.map fun rho => inv $ w - rho).sum) = (Z.map fun rho => re $ inv $ w - rho).sum := by
    simpa [map_map] using map_multiset_sum reAddGroupHom $ Z.map fun rho => inv $ w - rho
  rw [neg_re, sub_re, hsum'] at h1
  rw [add_re, neg_re, show w - 1 = mkC (σ - 1) t by simp [mkC]; ring] at hld
  rw [hld] at h1
  have hnn rho (hr_ : rho ∈ Z) : 0 ≤ re (inv (mkC σ t - rho)) := by
    have := mp not_le fun h => L1_ne_zero_of_one_le_re hxq_ h $ a2 $ mp (hZ rho) hr_
    rw [inv_re]
    exact div_nonneg (by simp
                         linarith) $ normSq_nonneg _
  have := sum_nonneg fun x hx => by
    obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
    exact hnn rho hr_
  refine ⟨hnn, ?_, ?_⟩ <;> (split_ifs at h1 ⊢ <;> simp only [one_div, zero_re] at h1 <;> linarith)

end

lemma zfr_nhds : ∃ del0 > r0, ∀ ⦃z : ℂ⦄, dist z 1 < del0 → riemannZeta₁ z ≠ 0 :=
  mp eventually_nhds_iff riemannZeta₁_ne_zero_of_near_one
def d0Z : ℝ := zfr_nhds.choose
def dZ : ℝ := min (inv (400 * ldC + 1200000)) (d0Z / 8)
def zfrC0 : ℝ := dZ / 40
lemma zfrC0_pos : 0 < zfrC0 := by
  have := a1 zfr_nhds.choose_spec
  have := ldC_nonneg
  dsimp [zfrC0, dZ]
  positivity
lemma zfrC0_le : zfrC0 ≤ 0.04 := by
  have : dZ ≤ inv (400 * ldC + 1200000) := min_le_left _ _
  have : inv (400 * ldC + 1200000) ≤ 0.04 := by
    rw [inv_eq_one_div, div_le_iff₀ $ by linarith [ldC_nonneg]]
    linarith [ldC_nonneg]
  dsimp [zfrC0]
  linarith

theorem zFRDirichlet (χ : DC q) (hxq_ : χ ≠ 1 ∨ q = 1) (s : ℂ) (hs : InRegion zfrC0 q s) (hz : IsLZero χ s) :
    χ ^ 2 = 1 ∧ χ ≠ 1 ∧ im s = 0 ∧ deriv (LFunction χ) s ≠ 0 ∧
    ∀ s', InRegion zfrC0 q s' → IsLZero χ s' → s' = s := by
  have hC0 := ldC_nonneg
  have hdZpos : 0 < dZ := by
    have := zfrC0_pos
    dsimp [zfrC0] at this
    linarith
  have hdZcS : dZ ≤ inv (400 * ldC + 1200000) := min_le_left _ _
  have hld1 {x : ℝ} (hx : 0 < x) : re (negLD (1 : DC 1) (cR (1 + x))) ≤ inv x + ldC := by
    have := le_trans (re_le_norm _) $ l_log_deriv_right (1 : DC 1) (s := cR $ 1 + x) $ by simp [hx]
    rwa [ofReal_re, add_sub_cancel_left, one_div] at this
  have h341 {r : ℕ} [NeZero r] (φ : DC r) (w : ℂ) (hfq : φ ≠ 1 ∨ r = 1)
      (hcase : φ ^ 2 ≠ 1 ∨ dZ / lcond r (im w) ≤ abs (im w)) (hreg : InRegion zfrC0 r w) : L1 φ w ≠ 0 := by
    intro hzero
    have hr := one_le_modulus_real r
    let a := dZ / 5
    have ha0 : 0 < a := by positivity
    have : (35400 + 6 * ldC) * a ≤ 0.25 := by
      have h1 : dZ ≤ 1 / (400 * ldC + 1200000) := by rwa [one_div]
      rw [le_div_iff₀ $ by linarith] at h1
      dsimp [a]
      nlinarith
    have : a ≤ 0.05 := by nlinarith
    let L := lcond r $ im w
    let al := a / L
    let la := L / a
    have hL : 0.5 < L := by linarith [lcond_ge_const r $ im w]
    have hLpos : 0 < L := by linarith
    have := div_pos hLpos ha0
    have hb1_ := mp not_le fun h => L1_ne_zero_of_one_le_re hfq h hzero
    let σ := 1 + al
    have hs1_ : 1 < σ := by linarith [div_pos ha0 hLpos]
    have hs11_ : σ ≤ 1.1 := by
      have : al ≤ 0.1 := mpr (div_le_iff₀ hLpos) $ by linarith
      linarith
    have hsb_ : σ - re w ≤ 1.125 * al := by
      dsimp [InRegion, zfrC0] at hreg
      dsimp [σ, al, a]
      ring_nf at hreg ⊢
      linarith
    have : re (negLD (1 : DC 1) σ) ≤ la + ldC := by
      simpa [σ, al, la, inv_div] using hld1 $ div_pos ha0 hLpos
    have hpole u (hu : dZ / L ≤ abs u) : re (inv $ mkC (σ - 1) u) ≤ 0.04 * la := by
      rw [mkC, inv_re, normSq_add_mul_I]
      simp [show σ - 1 = al by ring]
      grw [← show (dZ / L) ^ 2 ≤ al ^ 2 + u ^ 2 by nlinarith [sq_abs u, pow_le_pow_left₀ (by positivity) hu 2]]
      exact le_of_eq $ by field [ne_of_gt hdZpos, ne_of_gt hLpos]
    have h2 : re (negLD φ $ mkC σ $ im w) ≤ 0.04 * la + 5900 * L - 8 / 9 * la := by
      obtain ⟨Z, hZ, -, -, -, hb⟩ := L1_local_expansion φ hfq $ im w
      obtain ⟨hnn, h2', -⟩ := hb σ hs1_ hs11_
      rw [← cons_erase $ mpr (hZ w) ⟨by
        rw [mem_closedBall, dist_eq_norm, show w - mkC 1.05 (im w) = cR (re w - 1.05) by apply ext <;> simp, norm_real, norm_eq_abs, abs_le]
        exact ⟨by linarith, by linarith⟩, hzero⟩, map_cons, sum_cons] at h2'
      have hrest := sum_nonneg (s := (Z.erase w).map fun rho => re $ inv $ mkC σ (im w) - rho) fun x hx => by
        obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
        exact hnn rho $ mem_of_mem_erase hr_
      have : re (inv $ mkC σ (im w) - w) = 1 / (σ - re w) := by
        rw [show mkC σ (im w) - w = cR (σ - re w) by apply ext <;> simp, ← ofReal_inv, ofReal_re, one_div]
      have hu := (show 8 / 9 * la = 1 / (1.125 * al) by field [ne_of_gt ha0, ne_of_gt hLpos]).trans_le
        (one_div_le_one_div_of_le (by linarith) hsb_)
      split_ifs at h2' with hx1_
      linarith [hpole (im w) $ resolve_left hcase $ by simp [hx1_]]
      linarith
    have hlm2 : lcond r (2 * im w) ≤ 2 * L := by
      rw [lcond, show 2 * L = log ((r * (abs (im w) + 2)) ^ 2) by simp [L, lcond, log_pow], abs_mul, abs_two]
      exact log_le_log (by positivity) $ by nlinarith [abs_nonneg $ im w]
    have : (35400 + 6 * ldC) * L ≤ 0.25 * la := by
      rw [show (35400 + 6 * ldC) * L = (35400 + 6 * ldC) * a * la by field [ne_of_gt ha0]]
      nlinarith
    by_cases hsq : φ ^ 2 = 1
    obtain ⟨_, -, -, -, -, hb2⟩ := L1_local_expansion (1 : DC 1) (inr rfl) $ 2 * im w
    obtain ⟨-, -, hre2⟩ := hb2 σ hs1_ hs11_
    simp only [↓reduceIte] at hre2
    have : lcond 1 (2 * im w) ≤ 2 * L := le_trans (log_le_log (by positivity) $ by
      simp
      nlinarith [abs_nonneg $ im w]) hlm2
    have hP := negLD_341 φ (1 : DC 1) (fun n hu => by
      rw [Subsingleton.elim (n : ZMod 1) 1, map_one, ← pow_apply' φ two_ne_zero, hsq, one_apply hu]) hs1_ $ im w
    nlinarith [hpole (2 * im w) $ by rw [abs_mul, abs_two]; linarith [resolve_left hcase $ mpr not_not hsq, abs_nonneg $ im w]]
    obtain ⟨_, -, -, -, -, hb2⟩ := L1_local_expansion (φ ^ 2) (inl hsq) $ 2 * im w
    obtain ⟨-, -, hnr⟩ := hb2 σ hs1_ hs11_
    simp [hsq] at hnr
    have hP := negLD_341 φ (φ ^ 2) (fun n _ => pow_apply' φ two_ne_zero n) hs1_ $ im w
    nlinarith [lcond_pos r $ 2 * im w]
  have hL10 := mpr (L1_eq_zero_iff hxq_) hz
  have hx1_ : χ ≠ 1 := by
    rintro rfl
    obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not rfl
    by_cases hbig : dZ / lcond 1 (im s) ≤ abs (im s)
    exact h341 (1 : DC 1) s (inr rfl) (inr hbig) hs hL10
    push Not at hbig
    have := mp not_le fun h => L1_ne_zero_of_one_le_re (inr rfl) h hL10
    have : dZ / lcond 1 (im s) ≤ d0Z / 4 := mpr (div_le_iff₀ $ lcond_pos 1 $ im s) $ by
      nlinarith [show dZ ≤ d0Z / 8 from min_le_right _ _, lcond_ge_const 1 $ im s]
    have : 1 - re s ≤ d0Z / 4 := by
      dsimp [InRegion, zfrC0] at hs
      linarith [div_le_div_of_nonneg_right (show dZ / 40 ≤ dZ by linarith) $ le_of_lt $ lcond_pos 1 $ im s]
    exact a2 zfr_nhds.choose_spec (show dist s 1 < d0Z by
      have := norm_le_abs_re_add_abs_im $ s - 1
      simp [abs_of_neg $ show re s - 1 < 0 by linarith] at this
      rw [dist_eq_norm]
      linarith) $ by simpa [L1] using hL10
  have hsq := by_contra fun hsq => h341 χ s hxq_ (inl hsq) hs hL10
  have hsmall {w : ℂ} (hw : InRegion zfrC0 q w) (hwz : LFunction χ w = 0)  :=
    by_contra fun hlt => h341 χ w hxq_ (inr $ mp not_lt hlt) hw $ by simpa [L1, hx1_] using hwz
  have hq := one_le_modulus_real q
  let L0_ := lcond q 0
  have hL0h : 0.5 < L0_ := by linarith [lcond_ge_const q 0]
  have hL0pos : 0 < L0_ := by linarith
  let T := (40 * ldC + 120000) * L0_
  have hT10 : 10 ≤ T := by
    nlinarith only [hL0h, hC0]
  have hTpos : 0 < T := by positivity
  let σ := 1 + inv T
  have hs1_ : 1 < σ := lt_add_of_pos_right 1 $ mpr inv_pos hTpos
  have hs2 : σ ≤ 1.1 := by
    have := inv_anti₀ (by norm_num) hT10
    norm_num at this
    linarith only [this]
  have h0 : re (negLD (1 : DC 1) σ) ≤ T + ldC := by simpa [σ] using hld1 $ mpr inv_pos hTpos
  obtain ⟨Z, hZ, hmult, -, -, hb⟩ := L1_local_expansion χ (inl hx1_) 0
  simp only [L1, mkC, hx1_, ↓reduceIte, ofReal_zero, zero_mul, add_zero, zero_add] at hZ hmult hb
  obtain ⟨hnnZ, hb1, -⟩ := hb σ hs1_ hs2
  have hcons rho (hr : InRegion zfrC0 q rho) (hzr : LFunction χ rho = 0) :
      rho ∈ Z ∧ 0.75 * T ≤ re (inv $ σ - rho) := by
    have := hsmall hr hzr
    have hLr : L0_ ≤ lcond q (im rho) := log_le_log (by positivity) $ by simp; nlinarith only [hq, abs_nonneg $ im rho]
    have hdiv : dZ / lcond q (im rho) ≤ 0.1 / T :=
      le_trans (div_le_div_of_nonneg_right hdZcS $ le_of_lt $ lcond_pos q $ im rho)
        (trans_eq (div_le_div_of_nonneg_left (by positivity) hL0pos hLr) $ by
          field_simp [ne_of_gt hL0pos, ne_of_gt $ show 0 < 40 * ldC + 120000 by positivity]
          ring)
    have hb1_ := mp not_le fun h => LFunction_ne_zero_of_one_le_re χ (inl hx1_) h hzr
    have hb_ : 1 - 0.1 / T ≤ re rho := by
      unfold InRegion at hr
      have : zfrC0 ≤ dZ := by dsimp [zfrC0]
                              linarith only [hdZpos]
      linarith only [hr, hdiv, div_le_div_of_nonneg_right this $ le_of_lt $ lcond_pos q $ im rho]
    have hg_ : abs (im rho) ≤ 0.1 / T := by linarith
    have hsmall1 : 0.1 / T ≤ 0.01 := mpr (div_le_iff₀ hTpos) $ by linarith only [hT10]
    refine ⟨mpr (hZ rho) ⟨?_, hzr⟩, ?_⟩
    rw [mem_closedBall, dist_eq]
    refine le_trans (norm_le_abs_re_add_abs_im _) ?_
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    linarith only [hg_, hsmall1, (mpr abs_le ⟨by linarith only [hb_], by linarith only [hb1_, hg_, abs_nonneg $ im rho]⟩ : abs (re rho - 1.05) ≤ 0.05 + 0.1 / T)]
    rw [inv_re, normSq_apply]
    simp [neg_neg]
    have hB : T * (1 - re rho) ≤ 0.1 := by linarith only [mp (le_div_iff₀ hTpos) (by linarith only [hb_] : 1 - re rho ≤ 0.1 / T)]
    have hTg : abs (T * im rho) ≤ 0.1 := by rw [abs_mul, abs_of_pos hTpos]
                                            linarith only [mp (le_div_iff₀ hTpos) hg_]
    have hv : (T * im rho) ^ 2 ≤ 0.01 := by nlinarith only [sq_abs $ T * im rho, hTg, abs_nonneg $ T * im rho]
    have hTs : T * (σ - re rho) = T * (1 - re rho) + 1 := by dsimp [σ]
                                                             field_simp [ne_of_gt hTpos]
                                                             ring
    rw [le_div_iff₀ $ by nlinarith only [hs1_, hb1_, mul_self_nonneg $ im rho]]
    exact le_of_mul_le_mul_left (by nlinarith only [hB, hv, hTs, show 0 ≤ T * (1 - re rho) by positivity]) hTpos
  have hF1 : (Z.map fun rho => re $ inv $ σ - rho).sum < 1.5 * T := by
    have hP := negLD_341 χ (1 : DC 1) (fun n hu => by
      rw [Subsingleton.elim (n : ZMod 1) 1, map_one, ← pow_apply' χ two_ne_zero, hsq, one_apply hu]) hs1_ 0
    simp only [mkC, mul_zero, ofReal_zero, zero_mul, add_zero] at hP
    nlinarith only [hP, h0, hb1, hL0h, hC0]
  have htwo rho1 rho2 (h1r : InRegion zfrC0 q rho1) (h1z : LFunction χ rho1 = 0)
      (h2r : InRegion zfrC0 q rho2) (h2z : LFunction χ rho2 = 0) (h12 : rho2 ∈ Z.erase rho1) : False := by
    obtain ⟨h1Z, h1r'⟩ := hcons rho1 h1r h1z
    obtain ⟨-, h2r'⟩ := hcons rho2 h2r h2z
    rw [← cons_erase h1Z, ← cons_erase h12, map_cons, map_cons, sum_cons, sum_cons] at hF1
    linarith only [hF1, h1r', h2r', sum_nonneg (s := ((Z.erase rho1).erase rho2).map fun rho => re $ inv $ σ - rho) fun x hx => by
      obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
      exact hnnZ rho $ mem_of_mem_erase $ mem_of_mem_erase hr_]
  have hsim : im s = 0 := by
    by_contra hne
    have hconj0 : LFunction χ (starRingEnd ℂ s) = 0 := by
      have hL := differentiable_LFunction hx1_
      have hG : Differentiable ℂ $ fun z => starRingEnd ℂ $ LFunction χ $ starRingEnd ℂ z := fun z => by
        have := (hL $ starRingEnd ℂ z).conj_conj
        rwa [conj_conj] at this
      have heq := AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (analyticOnNhd_univ_iff_differentiable.2 hG)
          (analyticOnNhd_univ_iff_differentiable.2 hL) $ by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds $ show r1 < re 2 by norm_num] with z hz_
        rw [LFunction_eq_LSeries χ $ by rwa [conj_re], LFunction_eq_LSeries χ hz_, LSeries, LSeries, conj_tsum]
        congr 1
        funext m
        rw [term_def, term_def]
        split_ifs with hm
        norm_num
        have hconj : starRingEnd ℂ (χ m) = χ m := by
          rcases isQuadratic_iff_sq_eq_one.mpr hsq m with h | h | h <;> simp [h]
        rw [map_div₀, hconj, cpow_conj _ _ $ by simp [natCast_arg, symm pi_ne_zero], map_natCast (starRingEnd ℂ) m, conj_conj]
      rw [show LFunction χ (starRingEnd ℂ s) = starRingEnd ℂ (LFunction χ s) by simpa using (congrFun heq $ starRingEnd ℂ s).symm,
        a2 hz, _root_.map_zero]
    have hcr : InRegion zfrC0 q $ starRingEnd ℂ s := by simpa [InRegion, lcond] using hs
    exact htwo s _ hs (a2 hz) hcr hconj0
      (mpr (mem_erase_of_ne fun h => hne $ by have := congrArg im h; simp at this; linarith) $ a1 $ hcons _ hcr hconj0)
  refine ⟨hsq, hx1_, hsim, fun hd => htwo s s hs (a2 hz) hs (a2 hz) $ mp not_not fun h => mp (hmult s $ a1 $ hcons s hs $ a2 hz) h hd,
    fun s' hs' hz' => by_contra fun hne => htwo s s' hs (a2 hz) hs' (a2 hz') $ mpr (mem_erase_of_ne hne) $ a1 $ hcons s' hs' $ a2 hz'⟩

def zfrC : ℝ := 11800 + 48 / zfrC0
lemma zfrC_nonneg : 0 ≤ zfrC := by
  dsimp [zfrC]
  have := zfrC0_pos
  positivity

theorem log_deriv_in_zero_free_region (χ : DC q) (bet0 : Option ℝ) (hxq_ : χ ≠ 1 ∨ q = 1) (hB : ExcZeros zfrC0 χ bet0)
    (s : ℂ) (hs : InRegion (zfrC0 / 2) q s) (hs11 : re s ≤ 1.1) {δ : ℝ} (hd_ : 0 < δ)
    (hdP : ∀ p ∈ (if χ = 1 then some r1 else bet0), δ ≤ ‖s - cR p‖) :
    ‖negLD χ s‖ ≤ zfrC * lcond q (im s) ^ 2 + inv δ := by
  have hc1 := zfrC0_pos
  have := zfrC0_le
  obtain ⟨hBmem, hBall⟩ := hB
  let L := lcond q $ im s
  have := lcond_ge_const q $ im s
  have hLpos := lcond_pos q $ im s
  have : zfrC0 / 2 / L ≤ inv 34 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hsP p (hp : p ∈ (if χ = 1 then some r1 else bet0)) : s ≠ p := fun h => by
    have := hdP p hp
    rw [h, sub_self, norm_zero] at this
    linarith
  have hmono : InRegion zfrC0 q s := by
    unfold InRegion at hs ⊢
    linarith [div_le_div_of_nonneg_right (show zfrC0 / 2 ≤ zfrC0 by linarith) hLpos.le]
  have hfs : L1 χ s ≠ 0 := fun h0 => by
    obtain ⟨β, hb_, hsb⟩ := hBall s hmono $ mp (L1_eq_zero_iff hxq_) h0
    exact hsP β (by simp [a1 $ hBmem β hb_, hb_]) hsb
  obtain ⟨Z, hZ, hmult, hsum, hder, -⟩ := L1_local_expansion χ hxq_ $ im s
  let z0_ := mkC 1.05 $ im s
  have hs6 : s ∈ closedBall z0_ 0.08 := by
    rw [mem_closedBall, dist_eq_norm, show s - z0_ = cR (re s - 1.05) by apply ext <;> simp [z0_], norm_real, norm_eq_abs, abs_le]
    unfold InRegion at hs
    exact ⟨by linarith, by linarith⟩
  have hfar rho (hr_ : rho ∈ Z) (hne : ∀ β ∈ bet0, rho ≠ cR β) : inv ‖s - rho‖ ≤ 3 * L / zfrC0 := by
    obtain ⟨hball, hzero⟩ := mp (hZ rho) hr_
    have := mp not_le fun hreg => let ⟨β, hb_, hrb_⟩ := hBall rho hreg (mp (L1_eq_zero_iff hxq_) hzero)
      hne β hb_ hrb_
    have : abs (im rho - im s) ≤ 0.13 := by
      rw [mem_closedBall, dist_eq_norm] at hball
      simpa [z0_] using le_trans (abs_im_le_norm $ rho - z0_) hball
    have hLr : lcond q (im rho) ≤ 1.2 * L := by
      have := one_le_modulus_real q
      have : abs (im rho) ≤ abs (im s) + 0.13 := by linarith [abs_sub_abs_le_abs_sub (im rho) $ im s]
      have : lcond q (im rho) ≤ L + log 1.1 := by
        rw [← log_mul (by positivity) $ by norm_num]
        exact log_le_log (by positivity) $ by nlinarith [abs_nonneg $ im s]
      linarith [log_le_sub_one_of_pos $ show r0 < 1.1 by norm_num]
    have h1 := div_le_div_of_nonneg_left hc1.le (lcond_pos q $ im rho) hLr
    have hre : zfrC0 / (3 * L) ≤ re (s - rho) := by
      rw [sub_re]
      unfold InRegion at hs
      linarith [show zfrC0 / (3 * L) = zfrC0 / (1.2 * L) - zfrC0 / 2 / L by field [ne_of_gt hLpos]]
    exact trans_eq (inv_anti₀ (div_pos hc1 $ by linarith) $ le_trans hre $ re_le_norm _) $ inv_div _ _
  let D := 48 / zfrC0 * L ^ 2
  have hmsum Z' (hZ' : Z' ≤ Z) (hne : ∀ rho ∈ Z', ∀ β ∈ bet0, rho ≠ cR β) :
      ‖(Z'.map fun rho => inv $ s - rho).sum‖ ≤ D := by
    refine le_trans (by simpa [map_map] using norm_multiset_sum_le $ Z'.map fun rho => inv $ s - rho) ?_
    grw [sum_le_card_nsmul _ (3 * L / zfrC0) fun x hx => (by
        obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
        exact hfar rho (subset_of_le hZ' hr_) $ hne rho hr_),
      card_map, nsmul_eq_mul, show (Z'.card) ≤ rN Z.card from mpr cast_le $ card_le_card hZ', hsum]
    dsimp [D, L]
    ring_nf
    rfl
  let SZ := (Z.map fun rho => inv $ s - rho).sum
  have hSZ : ‖-SZ + (if χ = 1 then inv (s - 1) else 0)‖ ≤ D + inv δ := by
    by_cases h1 : χ = 1
    have hB0 : bet0 = none := mpr eq_none_iff_forall_ne_some fun β hb_ => a1 (hBmem β $ by simp [hb_]) h1
    simp [h1, ↓reduceIte]
    grw [norm_add_le, norm_neg, hmsum Z le_rfl fun _ _ _ h => by simp [hB0] at h, norm_inv,
      inv_anti₀ hd_ $ by simpa [h1] using hdP 1]
    simp [h1, ↓reduceIte, add_zero, norm_neg]
    by_cases hex : ∃ β ∈ bet0, cR β ∈ Z
    obtain ⟨β, hb_, hbZ⟩ := hex
    have hbm := hBmem β hb_
    dsimp [SZ]
    rw [← cons_erase hbZ, map_cons, sum_cons]
    grw [norm_add_le, norm_inv, inv_anti₀ hd_ $ hdP β $ by simp [h1, hb_],
      hmsum (Z.erase $ cR β) (erase_le _ _) fun rho hr_ bet' hb' h => by
        obtain rfl := Option.some.inj $ hb_.symm.trans hb'
        exact mpr (hmult _ hbZ) (by simpa [L1, a1 hbm] using hbm.2.2.2.2.2) $ h ▸ hr_]
    linarith
    linarith [hmsum Z le_rfl fun rho hr_ β hb_ h => hex ⟨β, hb_, h ▸ hr_⟩, mpr inv_pos hd_]
  rw [show negLD χ s = -(deriv (L1 χ) s / L1 χ s - SZ) + (-SZ + (if χ = 1 then inv (s - 1) else 0)) by
    rw [L1_log_deriv hxq_ (if h1 : χ = 1 then inr (by simpa [h1] using hsP 1) else inl h1) hfs]
    simp [one_div]
    ring]
  grw [norm_add_le, norm_neg, hder s hs6 hfs, hSZ]
  dsimp [zfrC, D]
  nlinarith

section
open scoped ComplexOrder LSeries.notation Nat

abbrev toAF {N : ℕ} (χ : DC N) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun m : ℕ => χ m)

lemma product_lfunction_key_inequality {q1 q2 : ℕ} [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (chi1 : DC q1) (chi2 : DC q2) (ψ : DC (q1 * q2))
    (h1 : chi1 ^ 2 = 1) (h2 : chi2 ^ 2 = 1) (h1ne : chi1 ≠ 1) (h2ne : chi2 ≠ 1) (hpne : ψ ≠ 1) (hp_ : ∀ n : ℕ, ψ n = chi1 n * chi2 n)
    {σ : ℝ} (hs1_ : 0.875 ≤ σ) (hs2 : σ < 1) (hzero : LFunction chi1 σ = 0) :
    1 - σ ≤ 2 * exp 15 * (‖LFunction chi1 1‖ * ‖LFunction chi2 1‖ * ‖LFunction ψ 1‖) * rN (q1 * q2) ^ (8 * (1 - σ)) := by
  let Q := rN (q1 * q2)
  let F s := riemannZeta s * LFunction chi1 s * LFunction chi2 s * LFunction ψ s
  let lam := LFunction chi1 1 * LFunction chi2 1 * LFunction ψ 1
  let d := 1 - σ
  have h1s_ : 0 < d := by linarith
  have := one_le_modulus_real q1
  have := one_le_modulus_real q2
  have : Q = rN q1 * q2 := by grind
  have : r1 ≤ Q := by nlinarith
  let f : ArithmeticFunction ℂ := zetaMul chi1 * (toAF chi2 * toAF ψ)
  have hvals {N : ℕ} (χ : DC N) (hx_ : χ ^ 2 = 1) x : 0 ≤ χ x ∨ χ x = -1 := by
    rcases mpr isQuadratic_iff_sq_eq_one hx_ x with h | h | h <;> simp [h]
  have hpp {N N' : ℕ} {χ : DC N} {chi' : DC N'} (hx_ : χ ^ 2 = 1)
      (hpm : ∀ n : ℕ, ψ n = χ n * chi' n) {p : ℕ} (hp : p.Prime)
      (hc : 0 ≤ chi' p ∨ (chi' p = -1 ∧ χ p = -1)) k :
      0 ≤ (zetaMul χ * (toAF chi' * toAF ψ)) (p ^ k) := by
    rw [mul_apply]
    refine sum_nonneg fun x hx => mul_nonneg (zetaMul_nonneg hx_ _) ?_
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 $ Dvd.intro_left _ $ a1 $ Nat.mem_divisorsAntidiagonal.1 hx
    rw [hj]
    have hconv : (toAF chi' * toAF ψ) (p ^ j) = chi' ((p ^ j : ℕ) : ZMod N') * zetaMul χ (p ^ j) := by
      rw [mul_apply, Nat.sum_divisorsAntidiagonal' fun a b => toAF chi' a * toAF ψ b, zetaMul, coe_zeta_mul_apply, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hdvd := Nat.dvd_of_mem_divisors hi
      simp only [toArithmeticFunction, coe_mk, ne_of_gt $ Nat.pos_of_mem_divisors hi, ne_of_gt $ Nat.div_pos (Nat.le_of_dvd (pow_pos hp.pos j) hdvd) $ Nat.pos_of_mem_divisors hi, ite_false, hpm i]
      rw [mul_left_comm, mul_comm $ χ _, ← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    rw [hconv, cast_pow, map_pow]
    rcases hc with h | ⟨h, h'⟩
    exact mul_nonneg (pow_nonneg h j) $ zetaMul_nonneg hx_ _
    rw [h, zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp,
      sum_congr rfl (g := fun i => (-1 : ℂ) ^ i) fun i _ => by simp [toArithmeticFunction, hp.ne_zero, h'], neg_one_geom_sum]
    split_ifs with he
    simp
    rw [((Nat.even_or_odd j).resolve_right fun ho => he ho.add_one).neg_one_pow]
    norm_num
  have hmul := (isMultiplicative_zetaMul chi1).mul
    ((isMultiplicative_toArithmeticFunction chi2).mul $ isMultiplicative_toArithmeticFunction ψ)
  have ha0 n : 0 ≤ f n := by
    rcases eq_or_ne n 0 with rfl | hn
    simp
    rw [IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]
    refine Finset.prod_nonneg fun p hp => ?_
    have hpr := prime_of_mem_primeFactors $ by simpa using hp
    rcases hvals chi2 h2 p with h | h
    exact hpp h1 hp_ hpr (inl h) _
    rcases hvals chi1 h1 p with h' | h'
    rw [show f = zetaMul chi2 * (toAF chi1 * toAF ψ) by
      simp [f, zetaMul, toAF]
      ring]
    exact hpp h2 (fun m => by rw [hp_ m, mul_comm]) hpr (inl h') _
    exact hpp h1 hp_ hpr (inr ⟨h, h'⟩) _
  have hls {N : ℕ} [NeZero N] (χ : DC N) {s : ℂ} (hs : 1 < re s) : LSeriesSummable ⇑(toAF χ) s :=
    mpr (LSeriesSummable_congr s fun {n} hn => by simp [toArithmeticFunction, hn]) $ LSeriesSummable_of_one_lt_re χ hs
  have hle {N : ℕ} [NeZero N] (χ : DC N) {s : ℂ} (hs : 1 < re s) : LSeries ⇑(toAF χ) s = LFunction χ s :=
    (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm.trans (LFunction_eq_LSeries χ hs).symm
  have hlt2 : abscissaOfAbsConv ⇑f < (re (2 : ℂ) : EReal) :=
    lt_of_le_of_lt (by
      simpa using abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1) fun y hy =>
        show LSeriesSummable (⇑(zetaMul chi1 * (toAF chi2 * toAF ψ))) _ from
          LSeriesSummable_mul (LSeriesSummable_zetaMul chi1 $ by simpa using hy)
            (LSeriesSummable_mul (hls chi2 (by simpa using hy)) (hls ψ (by simpa using hy))))
      (by exact_mod_cast (by norm_num))
  have hFa s (hs : 1 < re s) : F s = LSeries ⇑f s := by
    have h1s : LSeriesSummable ⇑(zeta : ArithmeticFunction ℂ) s :=
      mp (LSeriesSummable_congr s fun {n} hn => by simp [hn]) $ mpr LSeriesSummable_zeta_iff hs
    rw [LSeries_mul' (LSeriesSummable_zetaMul chi1 hs) $ LSeriesSummable_mul (hls chi2 hs) $ hls ψ hs,
      LSeries_mul' (hls chi2 hs) $ hls ψ hs, zetaMul, LSeries_mul' h1s $ hls chi1 hs, hle chi1 hs, hle chi2 hs, hle ψ hs,
      show L (fun n => (zeta : ArithmeticFunction ℂ) n) s = riemannZeta s from LSeries_zeta_eq_riemannZeta hs]
    ring
  let P s := LFunction chi1 s * LFunction chi2 s * LFunction ψ s
  let G := dslope (fun s => riemannZeta₁ s * P s) 1
  have hG : Differentiable ℂ G := by
    rw [← differentiableOn_univ]
    exact mpr (differentiableOn_dslope univ_mem)
      (differentiable_riemannZeta₁.mul $ ((differentiable_LFunction h1ne).mul $ differentiable_LFunction h2ne).mul $ differentiable_LFunction hpne).differentiableOn
  have hGs s (hs : s ≠ 1) : G s = (riemannZeta₁ s * P s - P 1) / (s - 1) := by
    dsimp only [G]
    rw [dslope_of_ne _ hs, slope_def_field, riemannZeta₁_one, one_mul]
  have hFG s (hs : s ≠ 1) : F s = G s + lam / (s - 1) := by
    rw [hGs s hs]
    simp [F, P, lam, riemannZeta_eq_inv_sub_mul hs]
    field [mpr sub_ne_zero hs]
  let B := 4000000 * Q ^ 2
  have hPw {w : ℂ} (hre : 0.5 ≤ re w) (hn : norm w ≤ 3.5) : ‖P w‖ ≤ 22.5 ^ 3 * Q ^ 2 := by
    have hLs (r : ℕ) [NeZero r] (χ : DC r) (hx_ : χ ≠ 1) : ‖LFunction χ w‖ ≤ 22.5 * r :=
      le_trans (lfunction_polynomial_growth χ hx_ w hre) $ by nlinarith [cast_nonneg (α := ℝ) r]
    simp only [P, norm_mul]
    grw [hLs q1 chi1 h1ne, hLs q2 chi2 h2ne, hLs (q1 * q2) ψ hpne]
    nlinarith
  have hB s (hs : s ∈ sphere (2 : ℂ) 1.5) : ‖G s‖ ≤ B := by
    have hsn := mp mem_sphere_iff_norm hs
    have hre : 0.5 ≤ re s := by
      linarith [re_le_norm $ 2 - s, show re (2 - s) = 2 - re s by simp, norm_sub_rev s 2]
    have hn : norm s ≤ 3.5 := by linarith [norm_sub_norm_le s 2, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hd : 0.5 ≤ ‖s - 1‖ := by
      have := norm_sub_le (s - 1) 1
      rw [show s - 1 - 1 = s - 2 by ring, hsn, norm_one] at this
      linarith
    have hs1 : s ≠ 1 := by
      rintro rfl
      norm_num at hsn
    rw [hGs s hs1, norm_div, div_le_iff₀ $ by linarith]
    grw [norm_sub_le, norm_mul, zeta1_growth_half hre, hn, hPw hre hn, hPw (w := 1) (by norm_num) $ by norm_num, ← hd]
    nlinarith [sq_nonneg Q]
  let M := ⌈100 + 8 * log Q⌉₊
  have hQlog : 0 ≤ log Q := log_nonneg $ by nlinarith
  have : 8 * B * 0.75 ^ M ≤ 1 := by
    have : 8 * B ≤ exp (25 + 2 * log Q) := by
      rw [exp_add, show 2 * log Q = rN 2 * log Q by norm_num, exp_nat_mul, exp_log $ by linarith]
      have : (32000000 : ℝ) ≤ exp 25 := le_trans (by norm_num) $
        trans_eq (pow_le_pow_left₀ zero_le_two (by linarith [add_one_le_exp 1] : 2 ≤ exp 1) 25) $ by rw [← exp_nat_mul]; norm_num
      nlinarith [sq_nonneg Q]
    grw [this, show (0.75 : ℝ) ≤ exp (-0.25) by linarith [add_one_le_exp (-0.25 : ℝ)], ← exp_nat_mul, ← exp_add]
    exact mpr exp_le_one_iff $ by linarith [Nat.le_ceil $ 100 + 8 * log Q]
  set x : ℝ := 2 - σ
  let xc := cR x
  have hcoef m : iteratedDeriv m (LSeries ⇑f) 2 = iteratedDeriv m G 2 + lam * ((-1) ^ m * cN $ m !) := by
    have hev : LSeries ⇑f =ᶠ[nhds (2 : ℂ)] fun s => G s + lam * inv (s - 1) :=
      eventually_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds $ by norm_num) fun s hs =>
        (hFa s hs).symm.trans $ by rw [hFG s fun h => by simp [h] at hs, div_eq_mul_inv]
    have hinv : ContDiffAt ℂ m (fun s => lam * inv (s - 1)) 2 := contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))
    rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_fun_add hG.contDiff.contDiffAt hinv,
      iteratedDeriv_const_mul_field, show (fun s : ℂ => inv $ s - 1) = fun z => inv (1 * z - 1) by simp]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
    norm_num
  let t n := inv (cN $ n !) • (cR σ - 2) ^ n • iteratedDeriv n G 2
  have hTt : HasSum t $ G σ := hasSum_taylorSeries_of_entire hG 2 σ
  have hsplit := hTt.summable.sum_add_tsum_nat_add M
  rw [hTt.tsum_eq] at hsplit
  let β n : ℂ := inv (cN $ n !) * ((-1) ^ n * iteratedDeriv n (LSeries ⇑f) 2)
  have hsx : cR σ - 2 = -xc := by
    dsimp [x, xc]
    push_cast
    ring
  have ht n : t n = xc ^ n * β n - lam * xc ^ n := by
    dsimp only [t, β]
    simp [hsx, neg_pow xc n, hcoef n]
    field_simp [mpr cast_ne_zero $ factorial_ne_zero n]
    rcases Nat.even_or_odd n with h | h <;> simp [h.neg_one_pow]
  let S := ∑ i ∈ range M, xc ^ i * β i
  let R := ∑' i, t (i + M)
  have hfin : ∑ i ∈ range M, t i = S - lam * ((xc ^ M - 1) / (xc - 1)) := by
    rw [sum_congr rfl fun i _ => ht i, sum_sub_distrib, ← mul_sum, geom_sum_eq $ mpr ofReal_ne_one $ by linarith]
  have hpos : 1 ≤ S := by
    have h0 := single_le_sum (fun i _ => mul_nonneg (pow_nonneg (by
        dsimp [xc, cR]
        exact_mod_cast (by linarith) : 0 ≤ xc) i)
      (mul_nonneg (mpr inv_nonneg (cast_nonneg _) : 0 ≤ inv (cN (i !))) (by simpa using iteratedDeriv_alternating ha0 (x := 2) hlt2 i)))
      (mpr mem_range $ mpr Nat.ceil_pos $ show 0 < 100 + 8 * log Q by positivity)
    have h1l : 1 ≤ LSeries ⇑f 2 := by
      rw [← (by simp [f, hmul.map_one] : term (⇑f) 2 1 = 1)]
      exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt2).le_tsum 1 fun j _ => by simpa using term_nonneg (ha0 j) 2
    rw [show xc ^ 0 * β 0 = LSeries ⇑f 2 by simp [β]] at h0
    exact le_trans h1l h0
  have : norm R ≤ 4 * B * 0.75 ^ M := by
    refine le_of_le_of_eq (tsum_of_norm_bounded (f := fun i => t $ i + M)
      ((hasSum_geometric_of_lt_one (r := 0.75) (by norm_num) $ by norm_num).mul_left $ B * 0.75 ^ M) fun i => ?_) (by norm_num
                                                                                                                      ring)
    let k := i + M
    have hx0 : 0 ≤ x := by linarith
    change ‖t k‖ ≤ _
    simp only [t, xc, smul_eq_mul, norm_mul, norm_inv, norm_pow, hsx, norm_neg, Complex.norm_natCast, norm_cR_nn hx0]
    grw [norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num) hG.diffContOnCl hB]
    rw [show inv (rN $ k !) * (x ^ k * (rN (k !) * B / 1.5 ^ k)) = B * (x / 1.5) ^ k by
      rw [div_pow x 1.5]
      field [mpr cast_ne_zero $ factorial_ne_zero k]]
    grw [show x / 1.5 ≤ 0.75 by
      rw [div_le_iff₀ $ by norm_num]
      linarith]
    rw [pow_add]
    ring_nf
    rfl
  have hkey : F σ = S - lam * cR (x ^ M / (x - 1)) + R := by
    rw [hFG σ $ mpr ofReal_ne_one $ ne_of_lt hs2, ← hsplit, hfin,
      show cR σ - 1 = -(xc - 1) by
        dsimp [x, xc]
        push_cast
        ring]
    have := mpr sub_ne_zero $ mpr ofReal_ne_one $ by linarith
    push_cast
    field_simp
    ring
  have hpow' : x ^ M ≤ exp 15 * Q ^ (8 * d) := by
    rw [rpow_def_of_pos $ by linarith, ← exp_add]
    refine le_trans (pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp d] : x ≤ exp d) M) ?_
    rw [← exp_nat_mul, exp_le_exp]
    have := Nat.ceil_lt_add_one $ show 0 ≤ 100 + 8 * log Q by positivity
    nlinarith
  have h2 : re (lam * cR (x ^ M / (x - 1))) ≤ exp 15 * norm lam * Q ^ (8 * d) / d := by
    refine le_trans (re_le_norm _) ?_
    rw [norm_mul, norm_cR_nn $ div_nonneg (pow_nonneg (by linarith) _) $ by linarith, show x - 1 = d by grind]
    grw [hpow']
    ring_nf
    rfl
  have hre := congrArg re hkey
  rw [show F σ = 0 by simp [F, hzero], zero_re, add_re, sub_re] at hre
  have hmain := mp (le_div_iff₀ h1s_) (by
    linarith [abs_re_le_norm R, neg_abs_le $ re R, show 1 ≤ re S by simpa using a1 $ mp le_def hpos] :
      0.5 ≤ exp 15 * norm lam * Q ^ (8 * d) / d)
  simp only [lam, norm_mul] at hmain
  linarith

end

theorem exceptional_zero_bound_of (ε : ℝ) (he_ : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DC q) (β : ℝ),
      χ ^ 2 = 1 → χ ≠ 1 → LFunction χ (cR β) = 0 → β ≤ 1 - c * rN q ^ (-ε) := by
  have he6 : 0 < ε / 6 := by linarith
  have he3 : 0 < ε / 3 := by linarith
  let sig0 := max 0.875 (1 - ε / 48)
  have hs01 : sig0 < 1 := max_lt (by norm_num) $ by linarith
  by_cases hex : ∃ (q1 : ℕ) (_ : NeZero q1) (chi1 : DC q1) (b1_ : ℝ),
      chi1 ^ 2 = 1 ∧ chi1 ≠ 1 ∧ sig0 ≤ b1_ ∧ b1_ < 1 ∧ LFunction chi1 (b1_) = 0
  obtain ⟨q1, _, chi1, b1_, h1sq, h1ne, hb10, hb11, hzero⟩ := hex
  let d := 1 - b1_
  have : 0 < d := by linarith
  have hKa : 8 * d ≤ ε / 6 := by grind
  let L1n := ‖LFunction chi1 1‖
  have hL1 := mpr norm_pos_iff $ LFunction_apply_one_ne_zero h1ne
  obtain ⟨d1, hd1, hd1ne⟩ := mp Metric.eventually_nhds_iff
    (((differentiable_LFunction h1ne).continuous.comp continuous_ofReal).continuousAt.eventually_ne
      (by simpa using LFunction_apply_one_ne_zero h1ne : (LFunction chi1 ∘ ofReal) 1 ≠ 0))
  have := one_le_modulus_real q1
  let r := min 0.25 $ ε / 6
  have hr4 : r ≤ 0.25 := min_le_left _ _
  have hr6 : r ≤ ε / 6 := min_le_right _ _
  let K1 := 9 + 6 / ε
  let K2 := (9 + 3 / ε) / r
  let D0 := 2 * exp 15 * L1n * K1 * rN q1 ^ (ε / 3)
  let c0 := d / D0
  let c := min (min r d1) $ c0 / K2
  have hc : 0 < c := by positivity
  refine ⟨c, hc, fun q _ χ β hx2 hx1_ hb_ => ?_⟩
  have hq1 := one_le_modulus_real q
  have hq0 : 0 < rN q := by linarith
  have hb1_ := mp not_le fun hge => LFunction_ne_zero_of_one_le_re χ (inl hx1_) (by simpa using hge) hb_
  have : rN q ^ (-ε) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hq1 $ by linarith
  by_cases hbh : β ≤ 1 - r
  have : c ≤ r := le_trans (min_le_left _ _) $ min_le_left _ _
  nlinarith
  push Not at hbh
  let c1_ := changeLevel (dvd_mul_right q1 q) chi1
  let c2_ := changeLevel (dvd_mul_left q q1) χ
  let ψ := c1_ * c2_
  by_cases hp1 : ψ = 1
  have hchg : c1_ = c2_ := by
    have hc2 : c2_ ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    rw [← mul_one c1_, ← hc2, sq, ← mul_assoc]
    dsimp [ψ] at hp1
    rw [hp1, one_mul]
  have hL1eq := LFunction_changeLevel (dvd_mul_right q1 q) chi1 (s := cR β) $ inl h1ne
  dsimp [c1_] at hchg
  rw [hchg, LFunction_changeLevel (dvd_mul_left q q1) χ (s := cR β) (inl hx1_), hb_, zero_mul] at hL1eq
  have hprod_ne : ∏ p ∈ (q1 * q).primeFactors, (1 - chi1 p * p ^ (-cR β)) ≠ 0 :=
    mpr prod_ne_zero_iff fun p hp h0 => by
      have hpr := prime_of_mem_primeFactors hp
      have h1 := congrArg norm (mp sub_eq_zero h0).symm
      rw [norm_one, norm_mul, norm_natCast_cpow_of_pos hpr.pos, neg_re, ofReal_re] at h1
      have := rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpr.one_lt : r1 < p) (by linarith : -β < 0)
      nlinarith [norm_le_one chi1 p, rpow_nonneg (cast_nonneg p) $ -β]
  have hge : d1 ≤ 1 - β := by_contra fun hlt =>
    hd1ne (by rw [Real.dist_eq, abs_of_neg $ by linarith]; linarith) $ (mp mul_eq_zero hL1eq.symm).resolve_right hprod_ne
  have : c ≤ d1 := le_trans (min_le_left _ _) $ min_le_right _ _
  nlinarith
  have hp_ (n : ℕ) : ψ n = chi1 n * χ n := by
    by_cases h : IsUnit (n : ZMod $ q1 * q)
    have h1 {r : ℕ} (hr : r ∣ q1 * q) (φ : DC r) : changeLevel hr φ (n : ZMod $ q1 * q) = φ (n : ZMod r) := by
      simpa [IsUnit.unit_spec, ZMod.cast_natCast hr] using changeLevel_eq_cast_of_dvd (χ := φ) hr h.unit
    rw [MulChar.mul_apply, h1, h1]
    rw [MulChar.map_nonunit _ h]
    rcases mp not_and_or $ by simpa [isUnit_iff_coprime, Nat.coprime_mul_iff_right] using h with h' | h' <;>
      simp [isUnit_iff_coprime, h']
  have hlogR {x a : ℝ} (hx : 1 ≤ x) (ha : 0 < a) : 9 + log x ≤ (9 + inv a) * x ^ a := by
    nlinarith [one_le_rpow hx ha.le, trans_eq (log_le_rpow_div (by linarith : 0 ≤ x) ha) $ div_eq_inv_mul _ _]
  have hlow : c0 * rN q ^ (-(ε / 3)) ≤ ‖LFunction χ 1‖ := by
    let Q := rN $ q1 * q
    have hN : Q = rN q1 * q := by grind
    have hN1 : 1 ≤ Q := by nlinarith
    have h2 := product_lfunction_key_inequality chi1 χ ψ h1sq hx2 h1ne hx1_ hp1 hp_ (le_trans (le_max_left _ _) hb10) hb11 hzero
    have hLp : ‖LFunction ψ 1‖ ≤ K1 * Q ^ (ε / 6) := by
      grw [lfunction_norm_near_one ψ hp1 le_rfl $ by norm_num,
        rpow_zero, mul_one, hlogR hN1 he6]
      rw [inv_div]
    have hNk := rpow_le_rpow_of_exponent_le hN1 hKa
    grw [hLp, hNk] at h2
    have hmulQ : Q ^ (ε / 6) * Q ^ (ε / 6) = rN q1 ^ (ε / 3) * rN q ^ (ε / 3) := by
      rw [← rpow_add $ by linarith, show ε / 6 + ε / 6 = ε / 3 by ring, hN, mul_rpow (by linarith) hq0.le]
    rw [rpow_neg hq0.le, ← div_eq_mul_inv, div_le_iff₀ $ rpow_pos_of_pos hq0 _, div_le_iff₀ $ by positivity]
    have : 2 * exp 15 * (L1n * ‖LFunction χ 1‖ * (K1 * Q ^ (ε / 6))) * Q ^ (ε / 6) = ‖LFunction χ 1‖ * rN q ^ (ε / 3) * D0 := by
      linear_combination 2 * exp 15 * L1n * K1 * ‖LFunction χ 1‖ * hmulQ
    linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (C := K2 * rN q ^ (2 * ε / 3)) (f := fun t => LFunction χ t)
    (f' := fun t => deriv (LFunction χ) t)
    (fun t _ => ((differentiable_LFunction hx1_ t).hasDerivAt.comp_ofReal).hasDerivWithinAt)
    (fun t ht => by
      have hC z (hz : z ∈ sphere (cR t) r) : ‖LFunction χ z‖ ≤ (9 + 3 / ε) * rN q ^ (2 * ε / 3) := by
        have hre := a1 $ mp abs_le $ trans_eq (abs_re_le_norm $ z - t) $ mp mem_sphere_iff_norm hz
        simp only [sub_re, ofReal_re] at hre
        grw [lfunction_norm_near_one χ hx1_ he3.le (by linarith [a1 ht]) (by linarith [a1 ht])
            (by linarith [norm_sub_norm_le z $ cR t, mp mem_sphere_iff_norm hz, norm_cR_nn $ by linarith [a1 ht], a2 ht]),
          hlogR hq1 he3]
        rw [mul_assoc, ← rpow_add hq0, inv_div]
        ring_nf
        rfl
      exact trans_eq (norm_deriv_le_of_forall_mem_sphere_norm_le (lt_min (by norm_num) he6) (differentiable_LFunction hx1_).diffContOnCl hC)
        (by dsimp [K2]; ring)) 1 ⟨le_of_lt hb1_, le_refl _⟩
  simp [hb_] at hmvt
  refine mp le_sub_comm ?_
  grw [show c ≤ c0 / K2 from min_le_right _ _,
    show rN q ^ (-ε) = rN q ^ (-(ε / 3)) / rN q ^ (2 * ε / 3) by rw [← rpow_sub hq0]
                                                                 ring_nf]
  rw [div_mul_div_comm, div_le_iff₀ $ by positivity]
  exact le_trans hlow $ trans_eq hmvt $ mul_comm _ _
  push Not at hex
  refine ⟨1 - sig0, by linarith, fun q _ χ β hx2 hx1_ hb_ => ?_⟩
  have := lt_of_not_ge fun hge => hex q inferInstance χ β hx2 hx1_ hge (mp not_le fun hge => LFunction_ne_zero_of_one_le_re χ (inl hx1_) (by simpa using hge) hb_) hb_
  have : rN q ^ (-ε) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (one_le_modulus_real q) $ by linarith
  nlinarith

section
variable {q : ℕ} [NeZero q]

lemma perron_formula_character (χ : DC q) (y : ℝ) (hy : 1 ≤ y) (sig0 : ℝ) (hs_ : 1 < sig0) :
    Integrable (fun t : ℝ => Fchi χ y (mkC sig0 t)) ∧
    Schi χ y = (inv (2 * π) : ℂ) * ∫ t : ℝ, Fchi χ y (mkC sig0 t) := by
  have hy0 : 0 < y := by linarith
  have hline : Continuous $ fun t => mkC sig0 t := by
    fun_prop
  have hnz {z : ℂ} (hz : 0 < re z) : z ≠ 0 := fun h => by simp [h] at hz
  have hw0 t : mkC sig0 t * (mkC sig0 t + 1) ≠ 0 := mul_ne_zero (hnz $ by simp; linarith) $ hnz $ by simp; linarith
  have hD t : 1 + t ^ 2 ≤ ‖mkC sig0 t * (mkC sig0 t + 1)‖ := by
    rw [← sq_le_sq₀ (by positivity) $ by positivity, Complex.sq_norm, map_mul, normSq_apply, normSq_apply]
    simp [mkC]
    nlinarith
  let K u t := cR u ^ mkC sig0 t / (mkC sig0 t * (mkC sig0 t + 1))
  let g x := cR $ max (1 - inv x) 0
  have hg0 {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : g x = 0 := by
    simp [g, max_eq_right $ mpr sub_nonpos $ mpr (one_le_inv₀ hx0) hx1]
  have hg_eq {w : ℂ} (hw : 1 < re w) :
      IntegrableOn (fun x => cR x ^ (-w - 1) • g x) (Ioi 1) ∧ mellin g (-w) = inv (w * (w + 1)) := by
    have ha1 : re (-w - 1) < -1 := by simp
                                      linarith
    have ha2 : re (-w - 2) < -1 := by simp
                                      linarith
    have h1 := integrableOn_Ioi_cpow_of_lt ha1 zero_lt_one
    have h2 := integrableOn_Ioi_cpow_of_lt ha2 zero_lt_one
    have heq : EqOn (fun x => cR x ^ (-w - 1) • g x) (fun x => cR x ^ (-w - 1) - cR x ^ (-w - 2)) $ Ioi 1 := fun x hx => by
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      simp only [g, smul_eq_mul, max_eq_left $ mpr sub_nonneg $ mpr (inv_le_one₀ hx0) hx.le]
      rw [show -w - 2 = (-w - 1) + -1 by ring, cpow_add _ _ $ mpr ofReal_ne_zero hx0.ne', cpow_neg_one]
      push_cast
      ring
    refine ⟨(h1.sub h2).congr_fun heq.symm measurableSet_Ioi, ?_⟩
    unfold mellin
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi zero_le_one)
        fun x hx => by simp [hg0 (a1 hx) $ mp not_lt $ a2 hx],
      setIntegral_congr_fun measurableSet_Ioi heq, integral_sub h1 h2,
      integral_Ioi_cpow_of_lt ha1 zero_lt_one, integral_Ioi_cpow_of_lt ha2 zero_lt_one]
    simp only [ofReal_one, one_cpow, show -w - 1 + 1 = -w by ring, show -w - 2 + 1 = -(w + 1) by ring]
    field [hnz $ show 0 < re w by linarith, hnz $ show 0 < re (w + 1) by simp; linarith]
  have hmc : MellinConvergent g ↑(-sig0) := by
    unfold MellinConvergent
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact (integrableOn_zero.congr_fun (fun x hx => by simp [hg0 (a1 hx) $ a2 hx]) measurableSet_Ioc).union
      ((a1 $ hg_eq (w := sig0) $ by simpa using hs_).congr_fun (fun _ _ => by simp) measurableSet_Ioi)
  have hneg t : mkC (-sig0) t = -mkC sig0 (-t) := by
    dsimp [mkC]
    push_cast
    ring
  have hm t : mellin g (mkC (-sig0) t) = inv (mkC sig0 (-t) * (mkC sig0 (-t) + 1)) := by
    rw [hneg, a2 $ hg_eq $ by simp [hs_]]
  have hsingle {u : ℝ} (hu : 0 < u) : g u = (inv (2 * π) : ℂ) * ∫ t : ℝ, K u t := by
    rw [← mellinInv_mellin_eq (-sig0) g hu hmc ((Integrable.mono' integrable_inv_one_add_sq (Continuous.inv₀ (by unfold mkC; fun_prop) fun t => hw0 $ -t).aestronglyMeasurable (of_forall fun t => by rw [Pi.inv_apply, norm_inv]; exact inv_anti₀ (by positivity) $ by simpa [neg_sq] using hD $ -t)).congr (of_forall fun t => (hm t).symm)) $ by unfold g; fun_prop (disch := exact ne_of_gt hu)]
    unfold mellinInv
    rw [integral_congr_ae (g := fun t => K u $ -t) $ of_forall fun t => by
        change cR u ^ (-mkC (-sig0) t) • mellin g (mkC (-sig0) t) = K u (-t)
        rw [hm, hneg, neg_neg, smul_eq_mul, ← div_eq_mul_inv],
      integral_neg_eq_self (K u) volume, real_smul]
    push_cast
    ring
  let f n := Λ n * χ n
  let G n t := term f (mkC sig0 t) n * K y t
  let Mn n := ‖term (fun k => (Λ k)) sig0 n‖ * y ^ sig0
  have hGn_le n t : ‖G n t‖ ≤ Mn n * inv (1 + t ^ 2) := by
    rcases eq_or_ne n 0 with rfl | hn
    simp [G, Mn]
    simp only [G, Mn, K, norm_mul, norm_div, norm_term_eq, hn, ↓reduceIte, f,
      norm_cpow_eq_rpow_re_of_pos hy0, mkC_re, ofReal_re]
    rw [div_eq_mul_inv $ y ^ sig0]
    grw [norm_le_one χ _, inv_anti₀ (by positivity) $ trans_eq (hD t) $ norm_mul _ _]
    ring_nf
    rfl
  have hGn_int n : Integrable (G n) volume := by
    rcases eq_or_ne n 0 with rfl | hn
    simp [G]
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul $ Mn n) ?_ $ of_forall $ hGn_le n
    simp only [G, K, term_of_ne_zero hn]
    exact ((continuous_const.div (hline.const_cpow $ inl $ mpr cast_ne_zero hn) fun t => by simp [hn]).mul
      ((hline.const_cpow $ inl $ mpr ofReal_ne_zero hy0.ne').div (by unfold mkC
                                                                     fun_prop) hw0)).aestronglyMeasurable
  have hSM := (LSeriesSummable_vonMangoldt (s := sig0) $ by simpa using hs_).norm.mul_right $ y ^ sig0
  have hGn_sum : Summable fun n => ∫ t : ℝ, ‖G n t‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun n => trans_eq (integral_mono (hGn_int n).norm (integrable_inv_one_add_sq.const_mul $ Mn n) $ hGn_le n)
        (by rw [integral_const_mul, integral_univ_inv_one_add_sq])) $ hSM.mul_right π
  have hF_eq : (fun t => Fchi χ y $ mkC sig0 t) = fun t => ∑' n, G n t := funext fun t => by
    rw [Fchi, mul_div_assoc, negLD_eq_LSeries_mul_vonMangoldt χ $ by simp [hs_], LSeries, ← tsum_mul_right]
    exact tsum_congr fun n => by simp [G, K, f, term_def, mul_comm $ χ n]
  let hMt t := hSM.mul_right $ inv $ 1 + t ^ 2
  refine ⟨hF_eq ▸ Integrable.mono' (integrable_inv_one_add_sq.const_mul (∑' n, Mn n))
    (aestronglyMeasurable_of_tendsto_ae atTop (fun _ => aestronglyMeasurable_fun_sum _ fun n _ => a1 $ hGn_int n)
      (of_forall fun t => (Summable.of_norm_bounded (hMt t) fun n => hGn_le n t).hasSum.tendsto_sum_nat))
    (of_forall fun t => trans_eq (tsum_of_norm_bounded (hMt t).hasSum fun n => hGn_le n t) tsum_mul_right), ?_⟩
  have hterm n : (inv (2 * π) : ℂ) * ∫ t, G n t = if n = 0 then 0 else f n * g (y / n) := by
    rcases eq_or_ne n 0 with rfl | hn0
    simp [G]
    have hn0' : r0 < n := by positivity
    have hGeq t : G n t = f n * K (y / n) t := by
      simp only [G, K, term_of_ne_zero hn0, f, ofReal_div, div_cpow_ofReal_nonneg hy0.le $ cast_nonneg n]
      push_cast
      ring
    simp only [hn0, ↓reduceIte, hGeq, integral_const_mul]
    rw [mul_left_comm, ← hsingle $ div_pos hy0 hn0']
  rw [hF_eq, ← integral_tsum_of_summable_integral_norm hGn_int hGn_sum, ← tsum_mul_left,
    tsum_eq_sum (s := Icc 1 ⌊y⌋₊) fun n hn => by
      rw [hterm]
      split_ifs with hn0
      rfl
      rw [mem_Icc] at hn
      have hn' : r0 < n := by positivity
      rw [hg0 (div_pos hy0 hn') $ mpr (div_le_one hn') (Nat.lt_of_floor_lt $ by omega).le, mul_zero]]
  unfold Schi Sa
  refine sum_congr rfl fun n hn => by
    rw [mem_Icc] at hn
    rw [hterm]
    simp [show n ≠ 0 by omega, g, f, max_eq_left $ mpr sub_nonneg $ mpr (div_le_one hy0) $ mp (Nat.le_floor_iff hy0.le) $ a2 hn]

lemma rectangle_contour_shift_character (χ : DC q)
    (hxq_ : χ ≠ 1 ∨ q = 1) (y : ℝ) (hy : 0 < y) (sig1 sig0 T : ℝ) (bet0 : Option ℝ)
    (hs1__ : 0 < sig1) (hs11__ : sig1 < 1) (hσ₀ : 1 < sig0) (hT : 0 < T) (hB1 : χ = 1 → bet0 = none)
    (hB : ∀ β ∈ bet0, sig1 < β ∧ β < sig0 ∧ LFunction χ (cR β) = 0 ∧ deriv (LFunction χ) (cR β) ≠ 0)
    (hZ : ∀ w, sig1 ≤ re w → re w ≤ sig0 → abs (im w) ≤ T → IsLZero χ w → ∃ β ∈ bet0, w = cR β) :
    rectInt (Fchi χ y) sig1 sig0 (-T) T =
      2 * π * I * ((if χ = 1 then cR y / 2 else 0) - elim bet0 0 (zterm y)) := by
  let K := uIcc sig1 sig0 ×ℂ uIcc (-T) T
  have hK {w} (hw : w ∈ K) : sig1 ≤ re w ∧ re w ≤ sig0 ∧ abs (im w) ≤ T := by
    rw [mem_reProdIm, Set.uIcc_of_le $ by linarith, Set.uIcc_of_le $ by linarith] at hw
    exact ⟨hw.1.1, hw.1.2, mpr abs_le $ a2 hw⟩
  let k z : ℂ := y ^ z / (z * (z + 1))
  have hkd : DifferentiableOn ℂ k {z | 0 < re z} := fun z hz =>
    ((DifferentiableAt.const_cpow differentiableAt_id $ inl $ mpr ofReal_ne_zero hy.ne').div
      (differentiableAt_id.mul $ differentiableAt_id.add_const 1)
      (mul_ne_zero (fun h => by simp [h] at hz) fun h => by
        have := congrArg re h
        simp at this
        linarith [show 0 < re z from hz])).differentiableWithinAt
  have hKsub : K ⊆ {z | 0 < re z} := fun w hw => show 0 < re w by linarith [a1 (hK hw)]
  have hPole p sgn (hp : sig1 < p ∧ p < sig0) (g : ℂ → ℂ) (hgd : Differentiable ℂ g)
      (hgne : ∀ w ∈ K, g w ≠ 0) (hld : ∀ w ∈ K, w ≠ p → negLD χ w = sgn * inv (w - p) - deriv g w / g w) :
      rectInt (Fchi χ y) sig1 sig0 (-T) T = 2 * π * I * (sgn * k p) := by
    let c := sgn * k p
    let A z := sgn * dslope k p z - deriv g z / g z * k z
    have hA : DifferentiableOn ℂ A K :=
      ((((differentiableOn_dslope ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp
                                                                                           linarith))).2 hkd).mono hKsub).const_mul sgn).sub
        ((hgd.deriv.differentiableOn.div hgd.differentiableOn hgne).mul $ hkd.mono hKsub)
    have hA0 : rectInt A sig1 sig0 (-T) T = 0 := by
      simpa only [smul_eq_mul, rectInt, mkC] using
        integral_boundary_rect_eq_zero_of_differentiableOn A ⟨sig1, -T⟩ ⟨sig0, T⟩ hA
    have hseg (z0 d : ℂ) (a b : ℝ) (hK' : ∀ t ∈ uIcc a b, z0 + t * d ∈ K ∧ z0 + t * d ≠ p)
        (F : ℂ → ℂ) (hF : ∀ t ∈ uIcc a b, HasDerivAt F (inv $ z0 + t * d - p) $ z0 + t * d) :
        d * ∫ t in a..b, Fchi χ y (z0 + t * d) =
          d * (∫ t in a..b, A (z0 + t * d)) + c * (F (z0 + b * d) - F (z0 + a * d)) := by
      let γ (t : ℝ) := z0 + t * d
      have hci : ContinuousOn (fun t => inv $ γ t - p) $ uIcc a b :=
        ContinuousOn.inv₀ (by fun_prop) fun t ht => mpr sub_ne_zero $ a2 $ hK' t ht
      have hci' := hci.intervalIntegrable (μ := volume)
      rw [integral_congr (g := fun t => A (γ t) + c * inv (γ t - p)) fun t ht => by
          obtain ⟨h1, h2⟩ := hK' t ht
          rw [Fchi, mul_div_assoc, hld _ h1 h2]
          dsimp [A, c, k]
          rw [dslope_of_ne _ h2, slope_def_field]
          field [mpr sub_ne_zero h2, hgne _ h1],
        integral_add (f := fun t => A $ γ t) (hA.continuousOn.comp (by fun_prop) fun t ht => a1 $ hK' t ht).intervalIntegrable $ hci'.const_mul c,
        intervalIntegral.integral_const_mul, mul_add, mul_left_comm d, ← intervalIntegral.integral_const_mul d fun t => inv $ γ t - p,
        integral_eq_sub_of_hasDerivAt (f := fun t => F $ γ t) (fun t ht => by
          simpa [smul_eq_mul, Function.comp_def, γ] using
            (hF t ht).scomp t $ ((hasDerivAt_id t).ofReal_comp.mul_const d).const_add z0) $ hci'.const_mul d]
    have hL {s} (hs : s - cR p ∈ slitPlane) : HasDerivAt (fun s => clog $ s - cR p) (inv $ s - cR p) s := by
      simpa using ((hasDerivAt_id s).sub_const $ cR p).clog hs
    have eH v (hv : v ∈ uIcc (-T) T) (hv0 : v ≠ 0) := by
      simpa [mkC, add_comm] using hseg (v * I) 1 sig1 sig0
        (fun x hx => ⟨mpr mem_reProdIm ⟨by simpa using hx, by simpa using hv⟩,
          fun h => hv0 $ by simpa using congrArg im h⟩)
        (fun s => clog $ s - cR p) fun _ _ => hL $ mpr mem_slitPlane_iff $ inr $ by simp [hv0]
    have eV x (hx : x ∈ uIcc sig1 sig0) (hxp : x ≠ p) F
        (hF : ∀ v ∈ uIcc (-T) T, HasDerivAt F (inv $ mkC x v - p) $ mkC x v) :=
      hseg x I (-T) T
        (fun v hv => ⟨mpr mem_reProdIm ⟨by simpa using hx, by simpa using hv⟩,
          fun h => hxp $ by simpa using congrArg re h⟩) F hF
    set a := mkC sig1 T - p
    set b := mkC sig1 (-T) - p
    have hP : clog a - clog (-a) = π * I := by
      apply ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos (x := a) $ by simp [a, hT]]
    have hM' : clog (-b) - clog b = π * I := by
      apply ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg (x := b) $ by simp [b, hT]]
    unfold rectInt at hA0 ⊢
    rw [eH (-T) left_mem_uIcc $ mpr neg_ne_zero hT.ne', eH T right_mem_uIcc hT.ne',
      eV sig0 right_mem_uIcc (ne_of_gt $ a2 hp) _ fun _ _ => hL $ mpr mem_slitPlane_iff $ inl $ by simp
                                                                                                   linarith,
      eV sig1 left_mem_uIcc (ne_of_lt $ a1 hp) (fun s => clog $ p - s) fun s _ =>
        (((hasDerivAt_id _).const_sub $ cR p).clog $ mpr mem_slitPlane_iff $ inl $ by simp; linarith).congr_deriv $ by
          rw [neg_div, ← div_neg, neg_sub, one_div]
          rfl,
      ← neg_sub $ mkC sig1 T, ← neg_sub $ mkC sig1 $ -T]
    linear_combination hA0 + c * (hP + hM')
  by_cases h1 : χ = 1
  obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
  subst h1
  rw [hB1 rfl]
  simp [↓reduceIte]
  have hzne w (hw : w ∈ K) : riemannZeta₁ w ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3⟩ := hK hw
    obtain ⟨β, hb_, -⟩ := hZ w h1 h2 h3 $ mp (L1_eq_zero_iff hxq_) $ by simpa [L1] using h0
    simp [hB1 rfl] at hb_
  rw [show y / 2 = 1 * k 1 by simp [k]; ring]
  refine hPole 1 1 ⟨hs11__, hσ₀⟩ riemannZeta₁ differentiable_riemannZeta₁ hzne fun w hw hw1 => ?_
  simp [ofReal_one] at hw1 ⊢
  have hld := L1_log_deriv hxq_ (inr hw1) $ by simpa [L1] using hzne w hw
  simp [L1] at hld ⊢
  linear_combination hld
  have hLd := differentiable_LFunction h1
  cases bet0 with
  | none =>
    simp [h1]
    have hLne w (hw : w ∈ K) : LFunction χ w ≠ 0 := fun h0 => by
      obtain ⟨h1', h2', h3'⟩ := hK hw
      obtain ⟨β, hb_, -⟩ := hZ w h1' h2' h3' ⟨inl h1, h0⟩
      simp at hb_
    simpa using hPole ((sig1 + sig0) / 2) 0 ⟨by linarith, by linarith⟩ (LFunction χ) hLd hLne
      fun _ _ _ => by simp [negLD]
  | some β =>
    obtain ⟨hb1_, hb2_, hbz, hbd_⟩ := hB β $ by simp
    simp only [h1, ↓reduceIte, elim_some, zero_sub]
    let g := dslope (LFunction χ) β
    have hgd : Differentiable ℂ g := mp differentiableOn_univ $ mpr (differentiableOn_dslope univ_mem) hLd.differentiableOn
    have hLz : (· - cR β) * g = LFunction χ := funext $ sub_smul_dslope_of_zero hbz
    have hgne w (hw : w ∈ K) : g w ≠ 0 := fun h0 => by
      rcases eq_or_ne w β with rfl | hne
      exact hbd_ $ by simpa [g, dslope_same] using h0
      obtain ⟨h1', h2', h3'⟩ := hK hw
      obtain ⟨bet', hb', hw'⟩ := hZ w h1' h2' h3' ⟨inl h1, by rw [← hLz]
                                                              simp [h0]⟩
      obtain rfl : β = bet' := by simpa using hb'
      exact hne hw'
    rw [show -zterm y β = (-1) * k β by simp [k, zterm]]
    refine hPole β (-1) ⟨hb1_, hb2_⟩ g hgd hgne fun w hw hwb => ?_
    rw [negLD, ← logDeriv_apply, ← hLz, logDeriv_mul (f := (· - cR β)) w (mpr sub_ne_zero hwb) (hgne w hw) (by fun_prop) $ hgd w,
      logDeriv_apply, logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
    ring

end

def smA0 : ℝ := 2 * π * exp 1 * (1 + ldC) + 2 * exp 1 * (zfrC + 1) + 4 * (zfrC + 24 / zfrC0) + 2
def smC : ℝ := smA0 * (2 * (4 / zfrC0) ^ 2)
lemma smC_nonneg : 0 ≤ smC := by
  have := ldC_nonneg
  have := zfrC_nonneg
  have := zfrC0_pos
  dsimp [smC, smA0]
  positivity

theorem smoothed_character_sum_of {q : ℕ} [NeZero q] (χ : DC q) (bet0 : Option ℝ) (y : ℝ)
    (hxq_ : χ ≠ 1 ∨ q = 1) (hB : ExcZeros zfrC0 χ bet0)
    (hy : 2 ≤ y) (hs10 : 10 ≤ slog y) (hq : rN q ≤ exp (zfrC0 / 4 * slog y)) :
    ‖Schi χ y - (if χ = 1 then cR y / 2 else 0) + elim bet0 0 (zterm y)‖ ≤
      smC * y * exp (-(zfrC0 / 4) * slog y) := by
  have hc1 := zfrC0_pos
  have hc1' := zfrC0_le
  have hC := zfrC_nonneg
  have hC₀ := ldC_nonneg
  have hB1 : χ = 1 → bet0 = none := fun h => mpr eq_none_iff_forall_ne_some fun β hb_ => a1 (a1 hB β (by simp [hb_])) h
  let p0_ : Option ℝ := if χ = 1 then some 1 else bet0
  have hq1 := one_le_modulus_real q
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hlogy : 0 < log y := log_pos $ by linarith
  let s := slog y
  let e1 := exp 1
  let c4 := zfrC0 / 4
  let T := exp $ zfrC0 * s / 2
  let L := log $ q * (T + 2)
  let X := exp $ -(zfrC0 * s / 2)
  have hl : log y = s ^ 2 := by grind
  have hs0 : 0 < s := by linarith
  have hT1 : 1 ≤ T := one_le_exp $ by positivity
  have hT0 : 0 < T := exp_pos _
  have hL2 : log 2 ≤ L := log_le_log two_pos $ by nlinarith
  have hL0 : 0 < L := by linarith [log_two_gt_d9]
  have hL4 : 4 * L ≤ s := by
    have hlogq : log q ≤ c4 * s := mpr (log_le_iff_le_exp $ by linarith) hq
    have hlogT : log (T + 2) ≤ 2 + zfrC0 * s / 2 := by
      rw [log_le_iff_le_exp $ by linarith, exp_add]
      nlinarith [add_one_le_exp 2]
    rw [show L = log q + log (T + 2) from log_mul (by linarith) $ by linarith]
    dsimp [c4] at hlogq
    nlinarith only [hlogq, hlogT, hc1', hs0, hs10]
  have hs1 : 1 ≤ s ^ 2 := by nlinarith only [hs10]
  have hLs2 : L ≤ s ^ 2 := by nlinarith only [hL4, hs10]
  have hL2s2 : L ^ 2 ≤ s ^ 2 := by nlinarith only [hL4, hL0]
  let u := zfrC0 / L
  have hu0 : 0 < u := div_pos hc1 hL0
  have hu1 : u ≤ 0.1 := mpr (div_le_iff₀ hL0) $ by linarith only [hc1', hL2, log_two_gt_d9]
  let sig1 := if ∀ p ∈ p0_, u / 24 ≤ abs (1 - u / 3 - p) then 1 - u / 3 else 1 - u / 4
  have hs1lo : 1 - u / 3 ≤ sig1 := by grind
  have hs1u : sig1 ≤ 1 - u / 4 := by grind
  have hs1Pu : ∀ p ∈ p0_, u / 24 ≤ abs (sig1 - p) := by
    dsimp [sig1]
    split_ifs with h
    exact h
    push Not at h
    obtain ⟨p, hp, hlt⟩ := h
    intro p' hp'
    obtain rfl : p = p' := Option.some.inj $ hp.symm.trans hp'
    have := abs_sub_le (1 - u / 3) p $ 1 - u / 4
    rw [abs_of_neg $ by linarith only [hu0], abs_sub_comm p] at this
    linarith only [this, hlt]
  have hhalf : 0.5 ≤ sig1 := by linarith
  have hs1lt1 : sig1 < 1 := by grind
  have hs1reg : 1 - zfrC0 / 2 / L ≤ sig1 := by grind
  let sig0 := 1 + inv (log y)
  have hs0gt : 1 < sig0 := by
    dsimp [sig0]
    linarith [mpr inv_pos hlogy]
  have hs011 : sig0 ≤ 1.1 := by
    have := inv_anti₀ (by norm_num : r0 < 100) (by nlinarith : 100 ≤ log y)
    norm_num at this
    linarith
  have hsdiff : abs (sig0 - sig1) ≤ 1 := by
    rw [abs_of_nonneg $ by linarith]
    linarith
  have hyσ₀ : y ^ sig0 = e1 * y := by
    rw [rpow_add hy0, rpow_one, rpow_def_of_pos hy0, mul_inv_cancel₀ hlogy.ne', mul_comm]
  have hyT : y / T = y * X := by
    rw [div_eq_mul_inv, ← exp_neg]
  have hWX : T * y ^ sig1 ≤ y * X := by
    rw [rpow_def_of_pos hy0, hl, ← exp_add]
    conv_rhs => rw [← exp_log hy0, hl, ← exp_add]
    refine mpr exp_le_exp ?_
    have h1 : zfrC0 ≤ (1 - sig1) * s := by
      dsimp [u] at hs1u
      have := mp (div_le_iff₀ hL0) $ show zfrC0 / L ≤ 4 * (1 - sig1) by linarith only [hs1u]
      nlinarith only [this, hL4, hs1u, hu0]
    nlinarith only [h1, hs0]
  have hlmono t (ht : abs t ≤ T) : lcond q t ≤ L :=
    log_le_log (by nlinarith [abs_nonneg t]) $ mul_le_mul_of_nonneg_left (by linarith) $ by linarith
  let keep := ∀ β ∈ bet0, sig1 < β
  let bf : Option ℝ := if keep then bet0 else none
  have hzer w (h1 : sig1 ≤ re w) (_ : re w ≤ sig0) (h3 : abs (im w) ≤ T) (h4 : IsLZero χ w) :
      ∃ β ∈ bf, w = cR β := by
    have hreg : InRegion zfrC0 q w := by
      unfold InRegion
      linarith only [h1, hs1lo, hu0, div_le_div_of_nonneg_left hc1.le (lcond_pos q $ im w) $ hlmono (im w) h3]
    obtain ⟨β, hbB, hwb⟩ := a2 hB w hreg h4
    have hlt := lt_of_le_of_ne (by simpa [hwb] using h1) fun h => by
      have := hs1Pu β $ by simp [p0_, a1 $ a1 hB β hbB, hbB]
      rw [h, sub_self, abs_zero] at this
      linarith
    have hk : keep := fun bet' hb' => Option.some.inj (hbB.symm.trans hb') ▸ hlt
    exact ⟨β, by simpa [bf, hk] using hbB, hwb⟩
  have hFbd w N Ym dden (hN : ‖negLD χ w‖ ≤ N) (hYm : y ^ re w ≤ Ym) (hdden : 0 < dden) (hdd : dden ≤ norm w * ‖w + 1‖) :
      ‖Fchi χ y w‖ ≤ N * Ym / dden := by
    have := le_trans (norm_nonneg _) hN
    unfold Fchi
    rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hy0]
    grw [← hdd, hN, hYm]
  have hpt w (hwT : abs (im w) ≤ T) (hre : 1 - zfrC0 / 2 / L ≤ re w) (hw11 : re w ≤ 1.1) δ (hd_ : 0 < δ)
      (hdP : ∀ p ∈ p0_, δ ≤ ‖w - p‖) Ym dden (hYm : y ^ re w ≤ Ym) (hdden : 0 < dden) (hdd : dden ≤ norm w * ‖w + 1‖) :
      ‖Fchi χ y w‖ ≤ (zfrC * L ^ 2 + inv δ) * Ym / dden := by
    have hreg : InRegion (zfrC0 / 2) q w := hre.trans' $ by linarith [div_le_div_of_nonneg_left (by linarith : 0 ≤ zfrC0 / 2) (lcond_pos q $ im w) $ hlmono (im w) hwT]
    refine hFbd w _ Ym dden (le_trans (log_deriv_in_zero_free_region χ bet0 hxq_ hB w hreg hw11 hd_ hdP) ?_) hYm hdden hdd
    have := (lcond_pos q $ im w).le
    grw [hlmono (im w) hwT]
  have hsqim z : im z ^ 2 ≤ norm z * ‖z + 1‖ :=
    (sq_abs $ im z).symm.trans_le $ by
      rw [sq]
      exact mul_le_mul (abs_im_le_norm z) (by simpa using abs_im_le_norm $ z + 1) (abs_nonneg _) $ norm_nonneg _
  let Ec := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y (mkC sig0 t)
  let V1 := ∫ v in (-T)..T, Fchi χ y (mkC sig1 v)
  let a := ∫ x in sig1..sig0, Fchi χ y (mkC x (-T))
  let b := ∫ x in sig1..sig0, Fchi χ y (mkC x T)
  have hI1 : norm Ec ≤ 2 * π * e1 * (1 + ldC) * s ^ 2 * (y * X) := by
    let B := (1 + ldC) * s ^ 2 * (e1 * y)
    have hB0 : 0 ≤ B := by positivity
    have hg := (integrable_inv_one_add_sq.comp_div hT0.ne').const_mul $ 2 * B / T ^ 2
    refine le_trans (le_trans (norm_integral_le_of_norm_le hg.integrableOn
      (ae_restrict_of_forall_mem measurableSet_Ioc.compl fun t ht => by
        have ht2 : T ^ 2 ≤ t ^ 2 := by
          simp at ht
          rcases le_or_gt t $ -T with h | h
          nlinarith only [h, hT0]
          nlinarith only [ht h, hT0]
        have ht2p : 0 < t ^ 2 := by nlinarith only [ht2, hT0]
        refine le_trans (hFbd (mkC sig0 t) _ (e1 * y) (t ^ 2)
          (by simpa [sig0, one_div, inv_inv] using l_log_deriv_right χ (s := mkC sig0 t) $ by simp [hs0gt])
          (by simp [hyσ₀]) ht2p $ by simpa using hsqim $ mkC sig0 t) ?_
        grw [show log y + ldC ≤ (1 + ldC) * s ^ 2 by nlinarith only [hl, hs1, hC₀]]
        rw [show 2 * B / T ^ 2 * inv (1 + (t / T) ^ 2) = 2 * B / (T ^ 2 + t ^ 2) by field_simp,
          div_le_div_iff₀ ht2p $ by positivity]
        nlinarith only [ht2, hB0]))
      (setIntegral_le_integral hg $ of_forall fun _ => by positivity)) $ le_of_eq ?_
    rw [integral_const_mul, Measure.integral_comp_div (fun x => inv $ 1 + x ^ 2) T,
      integral_univ_inv_one_add_sq, abs_of_pos hT0, ← hyT]
    dsimp [B]
    field_simp
  have hH v (hv : abs v = T) : ‖∫ x in sig1..sig0, Fchi χ y (mkC x v)‖ ≤ e1 * (zfrC + 1) * s ^ 2 * (y * X) := by
    grw [norm_integral_le_of_norm_le_const (C := (zfrC * L ^ 2 + 1) * (e1 * y) / T ^ 2)
      fun x hx => by
        rw [uIoc_of_le $ by linarith only [hs1lt1, hs0gt]] at hx
        simpa [inv_one] using hpt (mkC x v) (by simp [hv]) (by simpa using le_trans hs1reg (a1 hx).le)
          (by simpa using le_trans (a2 hx) hs011) 1 one_pos
          (fun p _ => le_trans hT1 $ by simpa [hv] using abs_im_le_norm $ mkC x v - p) (e1 * y) (T ^ 2)
          (by
            simp only [mkC_re, ← hyσ₀]
            exact rpow_le_rpow_of_exponent_le hy1 $ a2 hx)
          (sq_pos_of_pos hT0) $ by simpa [← sq_abs v, hv] using hsqim $ mkC x v,
      hsdiff, show zfrC * L ^ 2 + 1 ≤ (zfrC + 1) * s ^ 2 by nlinarith only [hL2s2, hC, hs1],
      ← show T ≤ T ^ 2 by nlinarith only [hT1]]
    rw [← hyT]
    ring_nf
    rfl
  have hV : norm V1 ≤ 4 * (zfrC + 24 / zfrC0) * s ^ 2 * (y * X) := by
    grw [norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := 2 * (zfrC * L ^ 2 + 24 * L / zfrC0) * y ^ sig1) fun v hv => by
        rw [uIoc_of_le $ by linarith only [hT0]] at hv
        have hF := hpt (mkC sig1 v) (by
            simp
            exact mpr abs_le ⟨(a1 hv).le, a2 hv⟩) (by simpa using hs1reg)
          (by
            simp
            linarith only [hs1lt1]) (u / 24) (by positivity)
          (fun p hp => le_trans (hs1Pu p hp) (by simpa using abs_re_le_norm $ mkC sig1 v - p)) (y ^ sig1) 0.5
          (by simp) (by norm_num)
          (by nlinarith only [hhalf, show sig1 ≤ norm (mkC sig1 v) by simpa using re_le_norm $ mkC sig1 v,
                show sig1 + 1 ≤ ‖mkC sig1 v + 1‖ by simpa using re_le_norm $ mkC sig1 v + 1])
        rwa [show (zfrC * L ^ 2 + inv (u / 24)) * y ^ sig1 / 0.5 = 2 * (zfrC * L ^ 2 + 24 * L / zfrC0) * y ^ sig1 by
          rw [inv_div]
          field [ne_of_gt hc1, ne_of_gt hL0]] at hF,
      hL2s2, hLs2]
    rw [show abs (T - -T) = 2 * T by rw [abs_of_pos $ by linarith only [hT0]]; ring,
      show 2 * (zfrC * s ^ 2 + 24 * s ^ 2 / zfrC0) * y ^ sig1 * (2 * T) = 4 * (zfrC + 24 / zfrC0) * s ^ 2 * (T * y ^ sig1) by ring]
    grw [hWX]
  have hrect := rectangle_contour_shift_character χ hxq_ y hy0 sig1 sig0 T bf (by linarith only [hhalf]) hs1lt1 hs0gt hT0
    (fun h => by
      dsimp [bf]
      split_ifs <;> simp [hB1 h])
    (fun β hb_ => by
      dsimp [bf] at hb_
      split_ifs at hb_ with hk
      obtain ⟨-, -, hb1_, -, hbz, hd⟩ := a1 hB β hb_
      exact ⟨hk β hb_, by linarith only [hb1_, hs0gt], hbz, hd⟩
      simp at hb_)
    hzer
  obtain ⟨hint, hperron⟩ := perron_formula_character χ y hy1 sig0 hs0gt
  rw [show ∫ t, Fchi χ y (mkC sig0 t) = (∫ t in (-T)..T, Fchi χ y (mkC sig0 t)) + Ec by
    rw [integral_of_le $ by linarith only [hT0], integral_add_compl measurableSet_Ioc hint]] at hperron
  unfold rectInt at hrect
  let R := (if χ = 1 then cR y / 2 else 0) - elim bf 0 (zterm y)
  let D0 := Schi χ y - R
  have halg : 2 * π * norm D0 ≤ norm Ec + norm a + norm b + norm V1 := by
    have hEq : cR (2 * π) * D0 = Ec + I * a - I * b + V1 := by
      dsimp [D0, R]
      rw [hperron]
      push_cast
      field_simp [pi_ne_zero]
      have := congrArg (I * ·) hrect
      simp only [mul_add, mul_sub, ← mul_assoc, I_mul_I, mul_left_comm I $ 2 * ↑π] at this
      linear_combination -this
    rw [← norm_cR_nn (x := 2 * π), ← norm_mul, hEq]
    linarith [norm_add_le (Ec + I * a - I * b) V1, norm_sub_le (Ec + I * a) $ I * b, norm_add_le Ec $ I * a,
      show ‖I * a‖ = norm a by simp, show ‖I * b‖ = norm b by simp]
  let O := elim bet0 0 (zterm y) - elim bf 0 (zterm y)
  have hO : norm O ≤ 2 * s ^ 2 * (y * X) := by
    refine le_trans (?_ : norm O ≤ 2 * y ^ sig1) $ by
      grw [← hs1, ← hWX, ← hT1]
      ring_nf
      rfl
    dsimp [O, bf]
    split_ifs with hk
    simp
    positivity
    cases hβ₀ : bet0 with
    | none =>
      simp
      positivity
    | some β =>
      have hbh := a1 $ a2 $ a1 hB β $ by simp [hβ₀]
      simp only [elim_some, elim_none, sub_zero]
      rw [show zterm y β = cR (y ^ β / (β * (β + 1))) by
          dsimp [zterm]
          rw [← ofReal_cpow hy0.le]
          push_cast
          rfl,
        norm_cR_nn, div_le_iff₀ $ by positivity]
      grw [rpow_le_rpow_of_exponent_le hy1 $ mp not_lt fun hlt => hk fun _ hb' => Option.some.inj (hβ₀.symm.trans hb') ▸ hlt, ← hbh]
      nlinarith only [hbh, rpow_nonneg hy0.le sig1]
  rw [show Schi χ y - (if χ = 1 then cR y / 2 else 0) + elim bet0 0 (zterm y) = D0 + O by
    ring]
  have hsum_le : ‖D0 + O‖ ≤ smA0 * (s ^ 2 * (y * X)) := by
    have hbot := hH (-T) $ by rw [abs_neg, abs_of_pos hT0]
    have htop := hH T $ abs_of_pos hT0
    dsimp [smA0, e1] at hI1 hbot htop hV ⊢
    linarith only [norm_add_le D0 O, le_mul_of_one_le_left (norm_nonneg D0) (by linarith [pi_gt_three] : r1 ≤ 2 * π), halg, hI1, hbot, htop, hV, hO]
  let v := c4 * s
  have hv : v ^ 2 * exp (-v) ≤ 2 := by
    rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ $ exp_pos v]
    linarith [quadratic_le_exp_of_nonneg $ show 0 ≤ v by positivity, show 0 ≤ v by positivity]
  refine le_trans hsum_le ?_
  rw [show X = exp (-v) * exp (-c4 * s) by
      dsimp [X, v, c4]
      rw [← exp_add]
      congr 1
      ring,
    show smA0 * (s ^ 2 * (y * (exp (-v) * exp (-c4 * s)))) = smA0 * ((4 / zfrC0) ^ 2 * (v ^ 2 * exp (-v))) * y * exp (-c4 * s) by
      field [ne_of_gt hc1]]
  have : 0 ≤ smA0 := by
    dsimp [smA0]
    positivity
  grw [hv]
  exact le_of_eq $ by dsimp [smC, c4, s]
                      ring

lemma exp_half_sq_le_mul_exp {y c0_ : ℝ} (hy : 2 ≤ y) (hc01 : c0_ ≤ 1) :
    exp (log y / 2) ≤ y * exp (-(c0_ / 4) * slog y) := by
  have := log_le_log two_pos hy
  have := sqrt_nonneg $ log y
  have : slog y ^ 2 = log y := sq_sqrt $ by linarith [log_two_gt_d9]
  conv_rhs => lhs; rw [← exp_log $ show 0 < y by linarith]
  rw [← exp_add]
  exact mpr exp_le_exp $ by nlinarith [log_two_gt_d9]

lemma second_diff_chebyshev_bound {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ Λ n)
    (M : ℝ → ℂ) (Z : ℂ) {c0_ Cs y : ℝ} (hc0 : 0 < c0_) (hc01 : c0_ ≤ 1)
    (hCs : 0 ≤ Cs) (hy : 2 ≤ y)
    (hM : let h := exp (-(c0_ / 2) * slog y)
      ‖cR (y * (1 + h)) * M (y * (1 + h)) - y * M y - cR (y * h) * Z‖ ≤ 2 * y ^ 2 * h ^ 2)
    (hE : ∀ z, y ≤ z → ‖Sa f z + M z‖ ≤ Cs * z * exp (-c0_ * slog z)) :
    ‖partialSumUpTo f y + Z‖ ≤ (33 / c0_ ^ 2 + 4 + 8 * Cs) * y * exp (-(c0_ / 4) * slog y) := by
  set L := log y
  set s := slog y
  set g := exp $ -(c0_ / 4) * s
  dsimp only at hM
  set h := exp $ -(c0_ / 2) * s
  let Y := y * (1 + h)
  have : 0 < L := by linarith [log_two_gt_d9, log_le_log two_pos hy]
  have : g ≤ 1 := mpr exp_le_one_iff $ mul_nonpos_of_nonpos_of_nonneg (by linarith) $ sqrt_nonneg _
  have hhg : h = g * g := by
    dsimp [h, g]
    rw [← exp_add]
    congr 1
    ring
  have : 0 < h := exp_pos _
  have : h ≤ g := by nlinarith [exp_pos $ -(c0_ / 4) * s]
  have hyY : y ≤ Y := by nlinarith
  have hErr z (hz1 : y ≤ z) (hz2 : z ≤ Y) : ‖cR z * (Sa f z + M z)‖ ≤ 2 * Cs * Y * y * h ^ 2 := by
    have hhexp : exp (-c0_ * slog z) ≤ h ^ 2 := by
      rw [sq, ← exp_add, exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left (sqrt_le_sqrt $ log_le_log (by linarith) hz1) $ le_of_lt hc0]
    have hz0 : 0 ≤ z := by linarith
    rw [norm_mul, norm_cR_nn hz0]
    grw [hE z hz1, hhexp, hz2, show z ≤ 2 * y by nlinarith]
    ring_nf
    rfl
  have hlog : log Y ≤ L + 1 := by
    rw [log_mul (by linarith) $ by linarith]
    linarith [log_le_sub_one_of_pos $ show 0 < 1 + h by linarith]
  have : L + 1 ≤ 2 * (y * g) := by linarith [add_one_le_exp $ L / 2, exp_half_sq_le_mul_exp hy hc01]
  have : g * (L + 1) ≤ 33 / c0_ ^ 2 := by
    have : g * (c0_ / 4 * s) ^ 2 ≤ 2 := by
      rw [show g = inv (exp $ c0_ / 4 * s) by dsimp [g]; rw [neg_mul, exp_neg], inv_mul_le_iff₀ $ exp_pos _]
      linarith [quadratic_le_exp_of_nonneg $ show 0 ≤ c0_ / 4 * s by positivity, show 0 ≤ c0_ / 4 * s by positivity]
    rw [le_div_iff₀ $ by positivity]
    nlinarith [show c0_ ^ 2 * L = 16 * (c0_ / 4 * s) ^ 2 by grind]
  let D := y * h
  have hws : ‖cR Y * Sa f Y - cR y * Sa f y - cR D * partialSumUpTo f y‖ ≤ (D + 1) * (D * (L + 1)) := by
    have hSa z (hz : 0 < z) : cR z * Sa f z = ∑ n ∈ Icc 1 ⌊z⌋₊, f n * cR (z - n) := by
      unfold Sa
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by
        push_cast
        field [mpr ofReal_ne_zero $ ne_of_gt hz]
    have hidw : cR Y * Sa f Y - cR y * Sa f y - cR D * partialSumUpTo f y = ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * cR (Y - n) := by
      rw [hSa Y $ by linarith, hSa y $ by linarith, partialSumUpTo, mul_sum,
        show Icc 1 ⌊Y⌋₊ = Icc 1 ⌊y⌋₊ ∪ Ioc ⌊y⌋₊ ⌊Y⌋₊ by
          have := floor_mono hyY
          ext k
          simp
          omega,
        sum_union $ Finset.disjoint_left.2 fun k => by simp
                                                       omega,
        add_sub_right_comm, add_sub_right_comm, ← sum_sub_distrib, ← sum_sub_distrib,
        Finset.sum_eq_zero fun n _ => by
          dsimp [D, Y]
          push_cast
          ring, zero_add]
    rw [hidw]
    have := log_nonneg $ show 1 ≤ Y by linarith
    grw [norm_sum_le, sum_le_card_nsmul _ _ (D * log Y) fun n hn => by
      rw [Finset.mem_Ioc] at hn
      have : y < rN n := by linarith [lt_floor_add_one y, (by exact_mod_cast a1 hn : rN ⌊y⌋₊ + 1 ≤ n)]
      have hn2 := le_trans (by exact_mod_cast a2 hn : rN n ≤ ⌊Y⌋₊) $ floor_le $ by linarith
      rw [norm_mul, norm_cR_nn]
      grw [hf n, vonMangoldt_le_log, log_le_log (by linarith) hn2, show Y - rN n ≤ D by linarith]
      exact le_of_eq $ mul_comm _ _, nsmul_eq_mul, hlog]
    gcongr
    rw [Nat.card_Ioc, Nat.cast_sub $ floor_mono hyY]
    linarith [floor_le $ show 0 ≤ Y by linarith, lt_floor_add_one y]
  refine le_of_mul_le_mul_left ?_ $ show 0 < D by positivity
  rw [show D * ‖partialSumUpTo f y + Z‖ = ‖cR D * (partialSumUpTo f y + Z)‖ by rw [norm_mul, norm_cR_nn],
    show cR D * (partialSumUpTo f y + Z) = -(Y * Sa f Y - cR y * Sa f y - cR D * partialSumUpTo f y) -
      (Y * M Y - cR y * M y - cR D * Z) + (Y * (Sa f Y + M Y) - cR y * (Sa f y + M y)) by
        ring]
  grw [norm_add_le, norm_sub_le, norm_neg, hws, hM, norm_sub_le, hErr Y hyY le_rfl, hErr y le_rfl hyY]
  have : D * (L + 1) ≤ y * g * (33 / c0_ ^ 2) := by
    dsimp [D]
    rw [hhg]
    nlinarith 
  have h2 : 4 * Cs * Y * y * h ^ 2 ≤ D * (8 * Cs * y * g) := by
    have h1h : (1 + h) * h ≤ 2 * g := by nlinarith
    have hnn : 0 ≤ 4 * Cs * y ^ 2 * h := by positivity
    nlinarith 
  have h3 : 0 ≤ D := by positivity
  have h4 : 0 ≤ 2 * D * y := by positivity
  have hD : D = y * h := rfl
  nlinarith

namespace AlpogeRHCore4

theorem siegelWalfisz :
    ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
        2 ≤ x → (q : ℝ) ≤ Real.log x ^ A →
          ‖(∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) -
            (if χ = 1 then (x : ℂ) else 0)‖ ≤
            C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  intro A hA
  let c0_ := zfrC0 / 4
  let c := c0_ / 4
  have hc0 : 0 < c0_ := div_pos zfrC0_pos (by norm_num)
  have hc01 : c0_ ≤ 1 := by
    dsimp [c0_]
    linarith [zfrC0_le]
  have hc : 0 < c := by positivity
  have hCs' := smC_nonneg
  let cbC := 33 / c0_ ^ 2 + 4 + 8 * smC + 18
  obtain ⟨cE, hcE, hEB⟩ := exceptional_zero_bound_of (inv $ 2 * A) $ by positivity
  obtain ⟨N, hN⟩ := mp eventually_atTop
    ((isLittleO_rpow_exp_pos_mul_atTop (2 * A) hc).bound one_pos)
  let U := max N 10
  let cf := min c cE
  let U2 := U ^ 2 + 1
  let eU := exp $ cf * U
  have hcf0 := lt_min hc hcE
  refine ⟨cf, cbC + U2 * eU, hcf0, fun q _ χ x hx hqL => ?_⟩
  let sx := slog x
  let E := x * exp (-cf * sx)
  let xc := cR x
  have hxpos : 0 < x := by linarith
  have hx0 := le_of_lt hxpos
  have hlx : 0 < log x := log_pos $ by linarith
  have hq1 := one_le_modulus_real q
  have hE0 : 0 ≤ E := by positivity
  rw [show (cbC + U2 * eU) * x * exp (-cf * sx) = cbC * E + U2 * eU * E by ring]
  by_cases hsmall : exp (c * sx) < log x ^ A ∨ sx < 10
  have hLU : sx ≤ U := by
    rcases hsmall with hsmall | h10
    by_contra hcon
    have h2 := hN sx $ le_trans (le_max_left _ _) $ le_of_lt $ mp not_le hcon
    rw [norm_of_nonneg $ by positivity, norm_of_nonneg $ exp_nonneg _,
      show sx ^ (2 * A) = log x ^ A by rw [rpow_mul $ sqrt_nonneg _, rpow_two, sq_sqrt $ le_of_lt hlx]] at h2
    linarith
    exact le_trans (le_of_lt h10) $ le_max_right _ _
  grw [norm_sub_le, show ‖if χ = 1 then xc else 0‖ ≤ x by split_ifs <;> simp [xc, norm_of_nonneg hx0, hx0],
    norm_sum_le, sum_le_card_nsmul _ _ (log x) fun n hn => by
      rw [norm_mul, norm_cR_nn vonMangoldt_nonneg]
      grw [norm_le_one χ _, vonMangoldt_le_log, log_le_log (mpr cast_pos $ a1 $ mp mem_Icc hn)
        (le_trans (mpr cast_le $ a2 $ mp mem_Icc hn) $ floor_le hx0)]
      simp, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, floor_le hx0,
    show log x ≤ U ^ 2 by nlinarith [sq_sqrt hlx.le, sqrt_nonneg $ log x]]
  have he : 1 ≤ eU * exp (-cf * sx) := by
    rw [← exp_add]
    exact one_le_exp $ by nlinarith
  refine le_add_of_nonneg_of_le (by positivity) ?_
  rw [show x * U ^ 2 + x = x * U2 by dsimp [U2]; ring,
    show U2 * eU * E = x * U2 * (eU * exp (-cf * sx)) by dsimp [E]; ring]
  exact le_mul_of_one_le_right (by positivity) he
  push Not at hsmall
  obtain ⟨hsmall, hs10⟩ := hsmall
  have hq := le_trans hqL hsmall
  let h := exp $ -(c0_ / 2) * sx
  let Ex := x * exp (-c * sx)
  let h1 := 1 + h
  have hexp {a : ℝ} (ha : cf ≤ a) : x * exp (-a * sx) ≤ E :=
    mul_le_mul_of_nonneg_left (mpr exp_le_exp $ by nlinarith) hx0
  have hExE : Ex ≤ E := by grind
  by_cases hx_ : χ = 1
  subst hx_
  simp
  have hZ1 : ExcZeros zfrC0 (1 : DC 1) none := ⟨by simp, fun s hs hz => absurd rfl (a1 $ a2 $ zFRDirichlet (1 : DC 1) (inr rfl) s hs hz)⟩
  let f : ℕ → ℂ := fun n => ↑(Λ n) * (1 : DC 1) n
  have hm := second_diff_chebyshev_bound (f := f) fun n => by simp [f, Subsingleton.elim (n : ZMod 1) 1, abs_of_nonneg vonMangoldt_nonneg]
    (fun z => -(z / 2)) (-xc) hc0 hc01 hCs' hx (by
      dsimp only
      rw [show cR (x * h1) * -(cR (x * h1) / 2) - xc * -(xc / 2) - cR (x * h) * -xc = -cR (x ^ 2 * h ^ 2 / 2) by dsimp [ h1]; push_cast; ring,
        norm_neg, norm_cR_nn]
      nlinarith )
    fun z hz => by
      simpa [sub_eq_add_neg, Schi, f, c0_] using smoothed_character_sum_of (1 : DC 1) none z (inr rfl) hZ1 (by linarith)
        (le_trans hs10 $ sqrt_le_sqrt $ log_le_log hxpos hz) $ by simpa using one_le_exp $ mul_nonneg (le_of_lt hc0) $ sqrt_nonneg _
  let S0 := (Icc 1 ⌊x⌋₊).filter fun n => ¬n.Coprime q ∧ Λ n ≠ 0
  let R := ∑ n ∈ S0, Λ n
  let K := Nat.log 2 ⌊x⌋₊
  have hpsi : partialSumUpTo (fun n => ↑(Λ n) * (1 : DC q) n) x - xc = (partialSumUpTo f x + -xc) - cR R := by
    rw [show (partialSumUpTo f x + -xc) - cR R = (partialSumUpTo f x - cR R) - xc by ring]
    congr 1
    simp only [f, R, S0, sum_filter]
    push_cast
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by
      rw [Subsingleton.elim (n : ZMod 1) 1, map_one, mul_one]
      by_cases h : n.Coprime q
      simp [h, one_apply $ (isUnit_iff_coprime n q).2 h]
      by_cases h2 : Λ n = 0 <;> simp [h, h2, MulChar.map_nonunit (1 : DC q) fun hu => h $ (isUnit_iff_coprime n q).1 hu]
  have hnc1 : R ≤ rN K * log q := trans_eq (sum_le_sum_of_subset_of_nonneg fun n hn => by
      rw [Finset.mem_filter, mem_Icc] at hn
      obtain ⟨p, k, hp, -, rfl⟩ := mp (isPrimePow_nat_iff n) $ mp vonMangoldt_ne_zero_iff $ hn.2.2
      exact mpr Nat.mem_divisors ⟨(pow_dvd_pow_of_dvd (by_contra fun hc => hn.2.1 $ Nat.Coprime.pow_left k $ mpr (Nat.Prime.coprime_iff_not_dvd hp) hc) k).trans $ pow_dvd_pow q $ Nat.le_log_of_pow_le one_lt_two $ le_trans (Nat.pow_le_pow_left hp.two_le k) $ hn.1.2, pow_ne_zero _ $ ne q⟩
    fun _ _ _ => vonMangoldt_nonneg) $ by rw [vonMangoldt_sum, cast_pow, log_pow]
  have hncb : rN K * log q ≤ 16 * Ex := by
    have hK : rN K * log 2 ≤ log x := by
      rw [← log_pow]
      exact log_le_log (by positivity) $ le_trans (by exact_mod_cast Nat.pow_log_le_self 2 (mpr Nat.floor_pos $ by linarith).ne') $ floor_le hx0
    have := log_nonneg hq1
    grw [show rN K ≤ 2 * log x by nlinarith only [hK, log_two_gt_d9, cast_nonneg (α := ℝ) K], mpr (log_le_iff_le_exp $ by linarith) hq,
      show c ≤ 0.25 by dsimp [c]
                       linarith [hc01]]
    nlinarith only [quadratic_le_exp_of_nonneg $ show 0 ≤ log x / 2 by linarith only [hlx],
      show sx ≤ log x by nlinarith only [sq_sqrt hlx.le, hs10], hlx, exp_half_sq_le_mul_exp hx hc01]
  rw [hpsi]
  have htri := trans_eq (norm_sub_le (partialSumUpTo f x + -xc) R) $ by rw [norm_cR_nn $ sum_nonneg fun _ _ => vonMangoldt_nonneg]
  refine le_add_of_le_of_nonneg ?_ $ by positivity
  nlinarith only [htri, hnc1, hncb, hm, hExE, hE0, show r0 ≤ 33 / c0_ ^ 2 + 4 + 8 * smC + 16 by positivity]
  simp [hx_]
  obtain ⟨bet0, hB⟩ : ∃ bet0, ExcZeros zfrC0 χ bet0 := by
    by_cases h : ∃ s, InRegion zfrC0 q s ∧ IsLZero χ s
    obtain ⟨s, hs, hL⟩ := h
    obtain ⟨-, -, him, hder, huniq⟩ := zFRDirichlet χ (inl hx_) s hs hL
    have hs' : s = cR (re s) := ext (by simp) $ by simp [him]
    have hhalf : 0.5 ≤ re s := by
      unfold InRegion at hs
      rw [him] at hs
      linarith [mpr (div_le_iff₀ (lcond_pos q 0)) (by linarith [lcond_ge_const q 0, zfrC0_le] : zfrC0 ≤ 0.5 * lcond q 0)]
    refine ⟨some $ re s, fun β hb_ => ?_, fun s' hs'' hL' => ⟨re s, by simp, (huniq s' hs'' hL').trans hs'⟩⟩
    obtain rfl : re s = β := by simpa using hb_
    rw [← hs']
    exact ⟨hx_, hhalf, mp not_le fun hge => LFunction_ne_zero_of_one_le_re χ (inl hx_) hge $ a2 hL, hs, a2 hL, hder⟩
    push Not at h
    exact ⟨none, by simp, fun s hs hL => absurd hL $ h s hs⟩
  let f : ℕ → ℂ := fun n => ↑(Λ n) * χ n
  let M z  := elim bet0 0 $ zterm z
  let Z  := elim bet0 0 fun β => xc ^ cR β / cR β
  have hM : ‖cR (x * h1) * M (x * h1) - xc * M x - cR (x * h) * Z‖ ≤ 2 * x ^ 2 * h ^ 2 := by
    cases hβ₀ : bet0 with
    | none =>
      simp [M, Z, hβ₀]
      positivity
    | some β =>
      obtain ⟨-, hb1_, hb2_, -⟩ := a1 hB β $ by simp [hβ₀]
      have hh1p : 0 < h1 := by positivity
      have hdiff0 : 0 ≤ h1 ^ (β + 1) - 1 - (β + 1) * h := by
        linarith [one_add_mul_self_le_rpow_one_add (s := h) (p := β + 1) (by linarith) $ by linarith]
      have hdiffu : h1 ^ (β + 1) - 1 - (β + 1) * h ≤ (β + 1) * h ^ 2 := by
        rw [rpow_add hh1p, rpow_one]
        nlinarith [rpow_one_add_le_one_add_mul_self (s := h) (p := β) (by linarith) (by linarith) $ le_of_lt hb2_]
      rw [show cR (x * h1) * M (x * h1) - xc * M x - cR (x * h) * Z = cR (x * x ^ β / (β * (β + 1)) * (h1 ^ (β + 1) - 1 - (β + 1) * h)) by
          simp only [M, Z, zterm, hβ₀, elim_some, xc]
          rw [← ofReal_cpow hx0, ← ofReal_cpow $ by positivity, mul_rpow hx0 $ le_of_lt hh1p, rpow_add hh1p, rpow_one]
          push_cast
          field [mpr ofReal_ne_zero $ show β ≠ 0 by linarith, show (β : ℂ) + 1 ≠ 0 by exact_mod_cast (by linarith)],
        norm_cR_nn]
      grw [show x ^ β ≤ x by simpa using rpow_le_rpow_of_exponent_le (by linarith) $ le_of_lt hb2_, ← hb1_, hdiffu]
      exact le_of_eq $ by field [show β + 1 ≠ 0 by linarith]
  have hm := second_diff_chebyshev_bound (f := f) fun n => by
      simp only [f, norm_mul, norm_cR_nn vonMangoldt_nonneg]
      exact mul_le_of_le_one_right vonMangoldt_nonneg $ norm_le_one χ _
    M Z hc0 hc01 hCs' hx hM fun z hz => by
      simpa [hx_, Schi, f, M, c0_] using smoothed_character_sum_of χ bet0 z (inl hx_) hB (by linarith)
        (le_trans hs10 $ sqrt_le_sqrt $ log_le_log hxpos hz)
        (le_trans hq (mpr exp_le_exp (by dsimp [c, c0_]
                                         nlinarith [sqrt_le_sqrt $ log_le_log hxpos hz, zfrC0_pos, sqrt_nonneg $ log z])))
  have : norm Z ≤ 2 * x * exp (-cE * sx) := by
    cases hβ₀ : bet0 with
    | none =>
      simp [Z, hβ₀]
      positivity
    | some β =>
      obtain ⟨-, hb1_, hblt1, hreg, hL0, -⟩ := a1 hB β $ by simp [hβ₀]
      have hb2_ := hEB q χ β (a1 $ zFRDirichlet χ (inl hx_) β hreg ⟨inl hx_, hL0⟩) hx_ hL0
      have hb0 : 0 < β := by positivity
      have hq0 : 0 < rN q := by positivity
      simp only [Z, hβ₀, elim_some]
      rw [norm_div, norm_cpow_eq_rpow_re_of_pos hxpos, ofReal_re, norm_cR_nn, div_le_iff₀ hb0]
      have h3 : cE ≤ (1 - β) * sx := by
        rw [rpow_neg $ le_of_lt hq0] at hb2_
        exact le_trans (mp (mul_inv_le_iff₀ $ rpow_pos_of_pos hq0 _) $ mp le_sub_comm hb2_)
          (mul_le_mul_of_nonneg_left (trans_eq (rpow_le_rpow (le_of_lt hq0) hqL $ by positivity) (by rw [← rpow_mul $ le_of_lt hlx, show A * inv (2 * A) = 1 / 2 by field_simp, ← sqrt_eq_rpow])) $ by linarith only [hblt1])
      have hxb : x ^ β ≤ x * exp (-cE * sx) := by
        rw [rpow_def_of_pos hxpos]
        conv_rhs => rw [← exp_log hxpos, ← exp_add]
        refine mpr exp_le_exp ?_
        have := mul_le_mul_of_nonneg_right h3 $ sqrt_nonneg $ log x
        rw [mul_assoc, mul_self_sqrt hlx.le] at this
        linarith only [this]
      nlinarith only [hb1_, hxb, rpow_pos_of_pos hxpos β]
  have htri := norm_sub_le (partialSumUpTo f x + Z) Z
  rw [add_sub_cancel_right] at htri
  rw [mul_assoc] at hm
  change ‖partialSumUpTo f x‖ ≤ _
  refine le_add_of_le_of_nonneg ?_ $ by positivity
  nlinarith [htri, hm, hExE, hexp $ min_le_right c cE, hE0, show r0 ≤ 33 / c0_ ^ 2 + 4 + 8 * smC by positivity]

end AlpogeRHCore4
