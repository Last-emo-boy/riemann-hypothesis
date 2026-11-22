import Mathlib

open Complex hiding log cos exp_sub cos_two_mul
open Real Metric MeasureTheory Set Filter Eventually Asymptotics ZetaAsymptotics LSeries HasSum Iff Or IsCompact AnalyticOnNhd DifferentiableOn IsBigO IsLittleO Int ArithmeticFunction IsOpen IsExactOn

abbrev hasZero (f : ℂ → ℂ) x := ∃ q, norm q ≤ 0.1 ∧ f q = 0 ∧ x ≤ -re q⁻¹

lemma landau {f x} M :
    x = 0 ∨ hasZero f x →
    DifferentiableOn ℂ f (closedBall 0 0.37182818286) →
    (∀ q, 0 ≤ re q → f q ≠ 0) →
    (∀ w, norm w ≤ 0.37182818286 → ‖f w‖ ≤ ‖f 0‖ * rexp M) →
    x - re (logDeriv f 0) ≤ 40 * M + 40 := by
  intro hx hd hz hb
  have hM : 0 ≤ M := by
    specialize hb 0 $ by norm_num
    simp_all
  rcases em $ hasZero f x with ⟨q, hr, hzero, hxq⟩ | has
  have hg := mpr (differentiableOn_dslope (c := q) $ closedBall_mem_nhds_of_mem $ by
    simp
    linarith) hd
  rw [← funext $ sub_smul_dslope_of_zero hzero] at hb hz ⊢
  simp at hz ⊢
  have := landau (M - 1) (inl rfl) hg (by grind) fun w hw => by
    apply norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
    apply diffContOnCl
    simpa
    intro u hu
    simp [frontier_closedBall'] at hu hb
    specialize hb u hu.le
    grw [← norm_sub_norm_le, hu, hr] at hb
    grw [exp_sub, exp_one_lt_d9]
    grind
    simpa
  specialize hz 0 le_rfl
  rw [logDeriv_fun_mul] <;> simp_all [logDeriv_apply, differentiableAt hg $ closedBall_mem_nhds 0 $ by norm_num]
  linarith
  obtain rfl := resolve_right hx has
  have nonzero z (hz' : z ∈ ball 0 0.1) hf := has ⟨z, by
    simp_all
    linarith, hf, by
    simp [div_nonpos_iff, normSq_nonneg]
    grind⟩
  have diff := mono hd (s := ball 0 0.1) $ by
    simp [subset_def]
    grind
  obtain ⟨g, hgz, hg⟩ := with_val_at (isExactOn_ball $ div (deriv diff isOpen_ball) diff nonzero) 0 0
  have hgd : DifferentiableOn ℂ g _ := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hfg⟩ := mp (logDeriv_eqOn_iff diff hgd.cexp isOpen_ball isPreconnected_ball
    (by simp) nonzero) fun z hz' => by simp [logDeriv_apply, (hg z hz').cexp.deriv]
  grw [zero_sub, neg_le_abs, abs_re_le_norm]
  refine le_of_tendsto (hg 0 $ by norm_num).tendsto_slope_zero.norm $
    mpr mem_nhdsWithin_iff ⟨0.05, by norm_num, by
      rintro z ⟨hz, hz0⟩
      simp [hgz] at hz hz0 ⊢
      grw [borelCaratheodory_zero (add_pos_of_nonneg_of_pos hM zero_lt_one) hgd]
      field_simp
      grw [hz]
      norm_num
      intro z hz'
      specialize hb z $ by
        simp_all
        linarith
      simp_all [hfg hz', @hfg 0 $ by norm_num, norm_exp]
      linarith
      norm_num
      simp
      linarith
      assumption⟩
termination_by ⌈M + 1⌉₊
decreasing_by simp [Nat.ceil_add_one hM]

lemma zetaBound s : 0.5 ≤ re s → 1 ≤ |im s| →
    ‖riemannZeta s‖ ≤ 2 + 2 * norm s := by
  intro hs h1
  let tail := indicator (Ioi 1) $ ofReal ∘ fract
  have hfb x : ‖ofReal $ fract x‖ ≤ 1 := by
    simp
    grind [abs_fract, fract_lt_one]
  grw [riemannZeta_eq_inv_sub_add,
    show riemannZeta₀ s = 1 - s * mellin tail (-s) by
      apply eqOn_of_preconnected_of_eventuallyEq
        (analyticOnNhd differentiable_riemannZeta₀.differentiableOn $ isOpen_re_gt 0)
        (analyticOnNhd fun z hz => by
            suffices DifferentiableAt ℂ (mellin tail) (-z) by fun_prop
            apply mellin_differentiableAt_of_isBigO_rpow (a := 0)
            apply (locallyIntegrableOn_const I).mono
            measurability
            filter_upwards
            rotate_left
            apply isBigO_of_le
            intro
            rotate_left
            simpa
            apply of_bound 0
            filter_upwards [Ioo_mem_nhdsGT zero_lt_one]
            grind [indicator_of_notMem, norm_zero]
            swap
            apply sub_one_lt
            all_goals simp
            all_goals grw [norm_indicator_le_norm_self]
            all_goals apply hfb
          (isOpen_re_gt 0))
        (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2)
      norm_num
      filter_upwards [mem_nhds (isOpen_re_gt 1) $ by norm_num] with z hz
      have h := LSeries_one_eq_riemannZeta hz ▸ LSeries_eq_mul_integral' 1 zero_le_one hz $ by
        simp
        rfl
      rw [setIntegral_congr_fun measurableSet_Ioi ?_, integral_sub] at h
      rotate_left
      apply integrableOn_Ioi_cpow_of_lt (a := -z)
      simpa
      norm_num
      apply Integrable.mul_bdd
      apply integrableOn_Ioi_cpow_of_lt (a := -z - 1)
      simp
      linarith
      norm_num
      swap
      exact of_forall hfb
      measurability
      intro x hx
      have hx0 := lt_trans zero_lt_one hx.out
      simp [fract, ← natCast_floor_eq_floor hx0.le, neg_add_eq_sub, cpow_sub, ne_of_gt hx0]
      grind [ofReal_eq_zero]
      grind
      rw [integral_Ioi_cpow_of_lt] at h
      rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi]
      simp at *
      grind [riemannZeta₀, one_re]
      simpa
      norm_num,
    norm_add_le, norm_sub_le, norm_inv, norm_mul, inv_le_one_of_one_le₀,
    mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi]
  · simp
    grw [norm_integral_le_of_norm_le, integral_Ioi_rpow_of_lt]
    rotate_right
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
    intros
    grw [norm_mul, hfb, norm_cpow_eq_rpow_re_of_pos]
    simp
    rfl
    simp_all
    linarith
    simp
    grw [← hs]
    rotate_right
    apply integrableOn_Ioi_rpow_of_lt
    all_goals grind
  grw [← abs_im_le_norm]
  simpa
  grind [one_im]

theorem AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / log (|im s| + 2) ≤ re s → riemannZeta s ≠ 0 := by
  obtain ⟨ep, hep, hball_p⟩ := mp mem_nhdsWithin_iff $
    bound log_deriv_riemannZeta_add_inv_sub_sub_isLittleO zero_lt_one
  obtain ⟨c_sh, hc_sh, hsh⟩ := exists_cthickening_subset_open (reProdIm isCompact_singleton isCompact_Icc)
    isClosed_riemannZetaZeros.isOpen_compl fun z hz => riemannZeta_ne_zero_of_one_le_re hz.left.ge
  refine ⟨min 0.00002 $ c_sh / 2, by positivity, fun s _ hre hz => ?_⟩
  let y := im s
  let Y := abs y + 2
  let lg := log Y
  have hY : 2 ≤ Y := by grind
  have := log_le_log two_pos hY
  have := log_two_gt_d9
  have hL0 : 0 < lg := by linarith
  have := lt_of_not_ge (riemannZeta_ne_zero_of_one_le_re · hz)
  rw [sub_le_comm, le_div_iff₀ hL0, le_min_iff] at hre
  by_cases hT : abs y ≤ max 3000 (rexp ep⁻¹)
  apply hsh _ hz
  apply mem_cthickening_of_dist_le _ ⟨1, im s⟩
  exact ⟨rfl, mp abs_le hT⟩
  simp [dist_eq_re_im, sqrt_sq_eq_abs, abs_le]
  constructor <;> nlinarith
  let sig := 1 + lg⁻¹ / 2000
  have := mul_inv_cancel₀ hL0.ne'
  have := mpr inv_pos hL0
  have hsig1 : 1 < sig := by grind
  have := le_trans (abs_re_le_norm _) $ hball_p ⟨by
    simp [sig, abs_of_pos hL0]
    grw [inv_lt_of_inv_lt₀ hep]
    linarith
    rw [lt_log_iff_exp_lt] <;> grind, mpr ofReal_ne_one hsig1.ne'⟩
  have hL t x0 : x0 = 0 ∨ hasZero (fun v => riemannZeta $ mk sig t + v) x0 →
      3 ≤ abs t ∧ abs t ≤ 2 * abs y →
      x0 - re (logDeriv riemannZeta $ mk sig t) ≤ 220 * lg := by
    intro hx0' h
    have hrz : 1 < re (mk sig t) := hsig1
    have : 1 ≤ ‖riemannZeta $ mk sig t‖ * Y ^ 2 := by
      have hS1 := mpr LSeriesSummable_one_iff hrz |>.norm
      have := zeta_limit_aux1 hsig1
      grw [← @norm_one ℂ, ← LSeries_one_mul_Lseries_moebius hrz, LSeries_one_eq_riemannZeta hrz,
        norm_mul, LSeries, tsum_of_norm_bounded hS1.hasSum]
      gcongr
      have : 0 ≤ termTSum sig := tsum_nonneg fun _ => term_nonneg _ _
      simp_rw [hS1.tsum_eq_zero_add, norm_term_eq]
      simp [sig, -inv_pos] at *
      nlinarith [log_le_sub_one_of_pos $ lt_of_lt_of_le two_pos hY]
      intro
      apply norm_term_le
      simp
      exact_mod_cast abs_moebius_le_one
    have := landau (log $ Y ^ 4) hx0'
      (comp differentiableOn_riemannZeta (by fun_prop) fun v hv => by
        simp_all [Complex.ext_iff]
        grind [abs_im_le_norm])
      fun r h => riemannZeta_ne_zero_of_one_le_re $ by
        simp
        linarith
      fun v hv => by
        grw [zetaBound, norm_add_le, norm_le_abs_re_add_abs_im, hv, ← le_exp_log]
        simp [abs_of_pos $ lt_trans zero_lt_one hsig1, sig]
        nlinarith
        all_goals simp
        all_goals grind [abs_re_le_norm, abs_im_le_norm]
    simp [logDeriv_apply, deriv_comp_const_add] at *
    linarith
  have hS k := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := mk sig k) hsig1 ▸
    hasSum_re (LSeriesSummable_vonMangoldt hsig1).LSeriesHasSum
  have := nonneg fun n => by
      cases n
      simp
      simp [div_eq_mul_inv, cpow_def_of_ne_zero, ← Complex.exp_neg, ← natCast_log, exp_re,
        mul_left_comm _ _ y, cos_two_mul, mul_assoc, ← mul_add, -Nat.cast_add]
      apply mul_nonneg
      positivity
      apply mul_nonneg
      positivity
      generalize cos _ = c
      nlinarith [sq_nonneg $ c + 1]
    (add (add (mul_right 3 $ hS 0) $ mul_right 4 $ hS y) $ hS $ 2 * y)
  have := hL (2 * y) 0 (inl rfl) $ by grind
  specialize hL y (1900 * lg) (inr ⟨ofReal $ re s - sig, by
    simp [sig, -ofReal_sub, abs_le]
    constructor <;> nlinarith,
    by
      convert hz
      simp [Complex.ext_iff, y],
    by
      norm_cast
      rw [← inv_neg, inv_eq_one_div, le_div_iff₀]
      dsimp [sig]
      nlinarith
      linarith⟩) $ by grind
  simp [mk_eq_add_mul_I, sig, logDeriv_apply, neg_div, abs_le] at *
  nlinarith [one_half_lt_eulerMascheroniConstant]
