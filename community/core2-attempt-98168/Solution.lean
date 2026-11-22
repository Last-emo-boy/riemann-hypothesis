import Mathlib

open Nat hiding add_le_add log card_univ lt_floor_add_one
open ZMod hiding map_smul cast_mul
open Submodule hiding map_comp mul_mem_mul mem_span_singleton mem_span_singleton_self span_singleton_eq_bot map_span span_singleton_eq_span_singleton span_singleton_le_iff_mem span
open Summable hiding norm
open Complex hiding log exp exp_add log_mul log_exp log_inv
open Real hiding norm_of_nonneg
open Int hiding log log_inv norm_eq_abs cast_nonneg cast_mul cast_pos cast_ne_zero
open Finset hiding Icc Ioc
open Subgroup hiding inv
open MulChar hiding inv
open Inv NumberField Filter Eventually Topology IsDedekindDomain Ideal Ideal.Quotient Set Function Algebra Module Fintype Metric HeightOneSpectrum IsCyclotomicExtension IntermediateField AlgEquiv RingHom Equiv ClassGroup RingOfIntegers FiniteField ZLattice Iff Prod Quotient MonoidHom Or QuasiFinite IsArithFrobAt

noncomputable section

open scoped Classical

abbrev DC := DirichletCharacter ℂ
abbrev Pr := Prime
abbrev nh1 := 𝓝[>] (1 : ℝ)
abbrev rN (n : ℕ) : ℝ := n
abbrev zN (n : ℕ) : ℤ := n
abbrev UZ := fun l ↦ (ZMod l)ˣ
abbrev sy := @Eq.symm
abbrev et := @Eq.trans
abbrev hl := @And.left
abbrev hr := @And.right
abbrev sext := @Subtype.ext
abbrev hext := @HeightOneSpectrum.ext
abbrev uext := @Units.ext
abbrev fo := @Fact.out
abbrev iqf := @Ideal.Quotient.field
abbrev tlt := @Summable.tsum_le_tsum
abbrev cl := Complex.log
abbrev d1 : DC 1 := 1
lemma nh1_f (h : ∀ᶠ _ in nh1, False) : False := h.exists.choose_spec

variable {E : Type} [Field E] [NumberField E] {l : ℕ} (chi : DC l)

section
variable (E)
abbrev Idl := Ideal $ 𝓞 E
abbrev Prm := HeightOneSpectrum $ 𝓞 E
end

abbrev qN (q : Prm E) := absNorm $ asIdeal q
abbrev qC (q : Prm E) := Coprime $ qN q
abbrev rp (s : ℝ) (a : Idl E) := rN a.absNorm ^ (-s)
abbrev rpq (s : ℝ) (q : Prm E) := rp s q.asIdeal
def cf (s : ℝ) (a : Idl E) := chi a.absNorm * (a.absNorm : ℂ) ^ (-(s : ℂ))

def under {E' : Type} [Field E'] [NumberField E'] [Algebra E E'] (P : Prm E') : Prm E :=
  ⟨P.asIdeal.under $ 𝓞 E, IsPrime.under _ _, under_ne_bot (𝓞 E) P.ne_bot⟩

theorem pa_cpow_eq (n : ℕ) (s : ℝ) : (n : ℂ) ^ (-(s : ℂ)) = ((n : ℝ) ^ (-s) : ℝ) := by
  simp [ofReal_cpow n.cast_nonneg]

lemma norm_cf_le {s : ℝ} {a : Idl E} : ‖cf chi s a‖ ≤ rp s a := by
  rw [cf, norm_mul, pa_cpow_eq, Complex.norm_of_nonneg $ by positivity]
  exact mul_le_of_le_one_left (by positivity) $ chi.norm_le_one _

lemma aN0 {I : Idl E} (h : I ≠ ⊥) : absNorm I ≠ 0 := absNorm_eq_zero_iff.not.mpr h

section

theorem two_le_Nrm (q : Prm E) : 2 ≤ qN q := by
  grind [aN0 q.ne_bot, absNorm_eq_one_iff.not.mpr q.isPrime.ne_top]

theorem Nrm_rpow_le_inv (q : Prm E) {s : ℝ} (hs : 1 ≤ s) : rpq s q ≤ inv (qN q : ℝ) := by
  rw [← rpow_neg_one]
  exact rpow_le_rpow_of_exponent_le (by exact_mod_cast le_trans one_le_two $ two_le_Nrm q) $ by linarith

theorem Nrm_rpow_le_half (q : Prm E) {s : ℝ} (hs : 1 ≤ s) : rpq s q ≤ 1 / 2 :=
  le_trans (Nrm_rpow_le_inv q hs) $ by
    rw [one_div]
    exact inv_anti₀ two_pos $ by exact_mod_cast two_le_Nrm q

lemma cont_cf {chi : DC l} {a : Idl E} (ha : a ≠ ⊥) : Continuous (cf chi · a) :=
  continuous_const.mul $ Continuous.const_cpow continuous_ofReal.neg $ inl $ mpr cast_ne_zero $ aN0 ha

section
variable (E)
def Lser (s : ℝ) := ∑' a : Idl E, cf chi s a
def Psum (s : ℝ) := ∑' q : Prm E, cf chi s q.asIdeal
def ab2 (s : ℝ) := ∑' q : Prm E, -cl (1 - cf chi s q.asIdeal)
def PE (s : ℝ) := ∑' q : Prm E, rpq s q
def Pcl (l : ℕ) (a : ZMod l) (s : ℝ) :=
  ∑' q : Prm E, indicator {q | (qN q : ZMod l) = a} (rpq s) q

section
variable {s : ℝ} (hs : 1 < s)
include hs

lemma hasSum_ideal :
    Summable (rp (E := E) s) ∧ dedekindZeta E s = Lser E d1 s := by
  let F n := {I : Idl E // absNorm I = n}
  let cF n := Nat.card (F n)
  have hterm n : LSeries.term (fun n ↦ (cF n : ℂ)) s n = ↑(rN (cF n) * n ^ (-s)) := by
    rcases eq_or_ne n 0 with rfl | hn
    simp [zero_rpow (by linarith : -s ≠ 0)]
    simp [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, pa_cpow_eq]
  obtain ⟨t, ht0, _, hts⟩ := (((tendsto_sub_one_mul_dedekindZeta_nhdsGT E).eventually_ne $
    mpr ofReal_ne_zero $ dedekindZeta_residue_ne_zero E).and $ Ioo_mem_nhdsGT hs).exists
  have hLs : LSeriesSummable (fun n ↦ (cF n : ℂ)) s :=
    LSeriesSummable.of_re_le_re (by simpa using le_of_lt hts) $ of_not_not $ mt tsum_eq_zero_of_not_summable $ right_ne_zero_of_mul ht0
  rw [LSeriesSummable, funext hterm] at hLs
  let e := sigmaFiberEquiv (absNorm : Idl E → ℕ)
  have (n : ℕ) : Finite (F n) := (finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
  have hfib n : ∑' x, rp s (e ⟨n, x⟩) = cF n * n ^ (-s) := by
    simp [rp, e, fun x : F n ↦ x.2, cF, F]
  have hsig := mpr (summable_sigma_of_nonneg (f := fun p ↦ rp s (e p)) fun _ ↦ by positivity)
    ⟨fun _ ↦ .of_finite, (mp summable_ofReal hLs).congr fun n ↦ sy $ hfib n⟩
  refine ⟨e.summable_iff.mp hsig, ?_⟩
  rw [dedekindZeta, LSeries, tsum_congr hterm, ← ofReal_tsum, ← tsum_congr hfib,
    ← hsig.tsum_sigma, e.tsum_eq, ofReal_tsum, Lser]
  exact tsum_congr fun _ ↦ by simp [cf, d1, MulChar.one_apply $ isUnit_of_subsingleton _, pa_cpow_eq]

theorem summable_prm_rpow : Summable fun q : Prm E ↦ rpq s q :=
  (hasSum_ideal E hs).left.comp_injective fun _ _ ↦ hext

theorem exp_ab2_eq_Lser :
    Complex.exp (ab2 E chi s) = Lser E chi s := by
  let f : Idl E →* ℂ := ⟨⟨cf chi s, by simp [cf]⟩, fun a b ↦ by
    simp [cf, natCast_mul_natCast_cpow]
    ring⟩
  have hsum := (hasSum_ideal E hs).left.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun _ ↦ norm_cf_le chi
  have hlt (q : Prm E) : ‖f q.asIdeal‖ < 1 := lt_of_le_of_lt (norm_cf_le chi) $ by linarith [Nrm_rpow_le_half q hs.le]
  let Sm (S : Finset $ Prm E) := {a : Idl E | a ≠ ⊥ ∧ ∀ q : Prm E, asIdeal q ∣ a → q ∈ S}
  let ind S := (Sm S).indicator f
  have hfin_prod (S : Finset (Prm E)) : HasSum (ind S) (∏ q ∈ S, inv (1 - f q.asIdeal)) := by
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty]
      exact (show ind ∅ 1 = 1 by
        refine (indicator_of_mem ?_ _).trans $ map_one f
        exact ⟨one_ne_zero, fun q hq ↦ (q.prime.not_isUnit $ isUnit_of_dvd_one hq).elim⟩) ▸
        hasSum_single 1 fun a ha ↦ by
          refine indicator_of_notMem ?_ _
          rintro ⟨ha0, hS⟩
          obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal a $ by rwa [← Ideal.one_eq_top]
          exact notMem_empty _ $ hS ⟨m, hm.isPrime, ne_bot_of_le_ne_bot ha0 ham⟩ $ mpr dvd_iff_le ham
    | insert q S hq ih =>
      rw [prod_insert hq]
      rw [← hasSum_subtype_iff_indicator] at ih ⊢
      set qi := asIdeal q
      let e : ℕ × Sm S → Sm (insert q S)
        | ⟨k, b⟩ => ⟨qi ^ k * b.1, mul_ne_zero (pow_ne_zero _ q.ne_bot) b.2.1, fun r hr ↦
            (r.prime.dvd_or_dvd hr).elim (fun h ↦ hext
              (mp (prime_dvd_prime_iff_eq r.prime q.prime) $ r.prime.dvd_of_dvd_pow h) ▸ mem_insert_self _ _)
              fun h ↦ mem_insert_of_mem $ b.2.2 r h⟩
      refine (ofBijective e ⟨fun ⟨k, b⟩ ⟨k', b'⟩ h ↦ by
        have h' := congrArg Subtype.val h
        have hm (m : ℕ) {c} (hc : ∀ r : Prm E, asIdeal r ∣ c → r ∈ S) : emultiplicity qi (qi ^ m * c) = m := by
          rw [emultiplicity_mul q.prime, emultiplicity_pow_self q.ne_bot q.prime.not_isUnit,
            mpr emultiplicity_eq_zero $ mt (hc q) hq, add_zero]
        obtain rfl : k = k' := cast_injective $ et (sy $ hm k b.2.2) $ et (congrArg (emultiplicity qi) h') $ hm k' b'.2.2
        exact Prod.ext rfl $ sext $ mul_left_cancel₀ (pow_ne_zero k q.ne_bot) h', fun ⟨a, ha, hsa⟩ ↦ by
        obtain ⟨k, b, hqb, hab⟩ := WfDvdMonoid.max_power_factor (a₀ := a) ha q.irreducible
        exact ⟨(k, ⟨b, fun h ↦ ha $ by simp [hab, h], fun p hp ↦
          (mp mem_insert $ hsa p $ hab ▸ dvd_mul_of_dvd_right hp _).elim (fun h ↦ absurd hp $ h ▸ hqb) id⟩),
          sext hab.symm⟩⟩).hasSum_iff.mp $ ((hasSum_geometric_of_norm_lt_one $ hlt q).mul ih $
        summable_mul_of_summable_norm (by simpa using summable_geometric_of_lt_one (norm_nonneg _) $ hlt q) $ hsum.subtype _).congr_fun fun ⟨_, _⟩ ↦ by simp [Equiv.ofBijective, e, qi]
  have hs1 : Summable fun q : Prm E ↦ f q.asIdeal := .of_norm_bounded (summable_prm_rpow E hs) fun _ ↦ norm_cf_le chi
  have hP := hs1.clog_one_sub.neg.hasSum.cexp
  have hp' (q : Prm E) : 1 - f q.asIdeal ≠ 0 := mpr sub_ne_zero fun h ↦ (hlt q).ne $ by simp [← h]
  simp [comp_def, Complex.exp_neg, Complex.exp_log $ hp' _] at hP
  apply hP.unique
  rw [HasProd, SummationFilter.unconditional_filter]
  simp_rw [← (hfin_prod _).tsum_eq]
  refine tendsto_tsum_of_dominated_convergence hsum (fun a ↦ tendsto_const_nhds.congr' ?_) $ of_forall fun _ _ ↦ norm_indicator_le_norm_self _ _
  by_cases ha0 : a = ⊥
  exact of_forall fun _ ↦ by simp [ind, Sm, ha0, f, cf, zero_cpow $ mpr neg_ne_zero $ mpr ofReal_ne_zero $ by linarith]
  have hfin := finite_factors (R := 𝓞 E) ha0
  filter_upwards [eventually_ge_atTop hfin.toFinset] with S hS
  refine sy $ indicator_of_mem ?_ _
  exact ⟨ha0, fun q hq ↦ hS $ hfin.mem_toFinset.mpr hq⟩

theorem ab2_sub_Psum :
    ‖ab2 E chi s - Psum E chi s‖ ≤ PE E 2 := by
  have hzs := of_norm_bounded (summable_prm_rpow E hs) fun _ ↦ norm_cf_le chi
  rw [ab2, Psum, PE, ← hzs.clog_one_sub.neg.tsum_sub hzs]
  refine tsum_of_norm_bounded (summable_prm_rpow E one_lt_two).hasSum fun q ↦ ?_
  set z := cf chi s q.asIdeal
  have := le_trans (norm_cf_le chi) (Nrm_rpow_le_half q hs.le)
  rw [← norm_neg, neg_sub, sub_neg_eq_add, add_comm, ← sub_neg_eq_add, sub_eq_add_neg 1]
  have : 0 ≤ inv (1 - norm z) := mpr inv_nonneg $ by linarith
  grw [norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]
                                                  linarith), norm_neg,
    inv_le_of_inv_le₀ two_pos $ by linarith,
    le_trans (norm_cf_le chi) $ Nrm_rpow_le_inv q hs.le]
  simp_all

end

def peC := PE E 2 + |log (dedekindZeta_residue E)| + 1

theorem pe_log_bdd : ∀ᶠ s in nh1, |PE E s - log (1 / (s - 1))| ≤ peC E := by
  have hres := dedekindZeta_residue_pos E
  filter_upwards [self_mem_nhdsWithin,
    ((continuousAt_log hres.ne').tendsto.comp $ by
      simpa [Real.norm_of_nonneg hres.le] using (continuous_norm.tendsto _).comp $
        tendsto_sub_one_mul_dedekindZeta_nhdsGT E).eventually $ ball_mem_nhds _ zero_lt_one] with s (hs : 1 < s) hball
  have hP : Psum E d1 s = ↑(PE E s) := by
    rw [Psum, PE, ofReal_tsum]
    exact tsum_congr fun _ ↦ by simp [cf, d1, MulChar.one_apply $ isUnit_of_subsingleton _, pa_cpow_eq]
  have he := congrArg norm $ exp_ab2_eq_Lser E d1 hs
  rw [norm_exp, ← hr $ hasSum_ideal E hs] at he
  have hd := le_trans (abs_re_le_norm _) $ ab2_sub_Psum E d1 hs
  rw [sub_re, hP, ofReal_re] at hd
  simp only [Real.dist_eq, Function.comp_apply] at hball
  rw [norm_mul, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg $ by linarith,
    log_mul (by linarith) $ he ▸ (exp_pos _).ne', ← he, log_exp] at hball
  rw [one_div, log_inv, peC]
  grind

lemma finite_not_coprime (n : ℕ) (hn : n ≠ 0) :
    {q : Prm E | ¬ qC q n}.Finite := by
  refine (finite_factors (by simpa using hn : span {↑n} ≠ 0)).subset fun q hq ↦ mpr dvd_span_singleton ?_
  set qi := asIdeal q
  let := iqf qi
  let := ofFinite $ 𝓞 E ⧸ qi
  obtain ⟨k, hcp, hcard⟩ := card (𝓞 E ⧸ qi) _
  rw [← eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝓞 E ⧸ qi) _]
  exact of_not_not fun hd ↦ hq $ by
    rw [qC, qN, absNorm_apply, cardQuot_apply, card_eq_fintype_card, hcard]
    exact Coprime.pow_left _ $ hcp.coprime_iff_not_dvd.mpr hd

end

end

theorem fibre_sum_le {al be ga : Type*} (pi : al → be) (emb : al → ga) (hemb : Injective emb)
    (B : be → Set ga) {f : al → ℝ} (h : be → ℝ) (n : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hfh : ∀ a, f a ≤ h (pi a)) (hh0 : ∀ b, 0 ≤ h b) (hh : Summable h)
    (hBm : ∀ a, emb a ∈ B (pi a)) (hfib : ∀ b, (B b).Finite ∧ (B b).ncard ≤ n) :
    Summable f ∧ ∑' a, f a ≤ n * ∑' b, h b := by
  let e := sigmaFiberEquiv pi
  have hA b : MapsTo emb {a | pi a = b} $ B b := fun a ha ↦ ha ▸ hBm a
  have (b : be) : Fintype {a // pi a = b} := (((hl $ hfib b).preimage hemb.injOn).subset $ hA b).fintype
  have hfb b : ∑' x : {a // pi a = b}, f x ≤ n * h b := by
    rw [tsum_fintype]
    refine le_trans (sum_le_sum fun x _ ↦ x.2 ▸ hfh x) ?_
    rw [sum_const, card_univ, nsmul_eq_mul, ← card_eq_fintype_card]
    gcongr
    exact hh0 b
    exact_mod_cast le_trans (ncard_def _ ▸ ncard_le_ncard_of_injOn _ (hA b) hemb.injOn (hl $ hfib b)) $ hr $ hfib b
  have hs2 := (hh.mul_left ↑n).of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ hf0 _) hfb
  have hsig : Summable fun p ↦ f $ e p := mpr (summable_sigma_of_nonneg fun _ ↦ hf0 _) ⟨fun _ ↦ .of_finite, hs2⟩
  exact ⟨e.summable_iff.mp hsig, by
    rw [← e.tsum_eq, hsig.tsum_sigma, ← tsum_mul_left]
    exact tlt hfb hs2 $ hh.mul_left ↑n⟩

theorem tendsto_log_one_div_sub_one : Tendsto (fun s ↦ log $ 1 / (s - 1)) nh1 atTop := by
  simp_rw [one_div]
  exact tendsto_log_atTop.comp $ tendsto_inv_nhdsGT_zero.comp $ mpr tendsto_nhdsWithin_iff
    ⟨by simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun _ h ↦ mpr mem_Ioi $ mpr sub_pos h⟩

section

open NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem ComplexEmbedding

abbrev mN := @mixedEmbedding.norm

def tent (t : ℝ) := max 0 (1 - abs t)
def Tent {it : Type*} [Fintype it] (y : it → ℝ) := ∏ i, tent (y i)

lemma tent0 (t : ℝ) : 0 ≤ tent t := le_max_left _ _

lemma msm (a b c d : ℝ) : a * b - c * d = a * (b - d) + (a - c) * d := by ring

lemma abs_Tent_sub {it : Type*} [Fintype it] (y y' : it → ℝ) :
    |Tent y - Tent y'| ≤ ∑ i, |y i - y' i| := by
  unfold Tent
  generalize (univ : Finset it) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj, msm]
    grw [abs_add_le, abs_mul, abs_mul, abs_of_nonneg $ tent0 _, abs_of_nonneg $ prod_nonneg fun _ _ ↦ tent0 _]
    refine (add_le_add ?_ ?_).trans_eq $ add_comm _ _
    exact le_trans (mul_le_of_le_one_left (abs_nonneg _) $ max_le zero_le_one $ by grind) ih
    exact le_trans (mul_le_of_le_one_right (abs_nonneg _) $ prod_le_one₀ (fun _ _ ↦ tent0 _) fun _ _ ↦ max_le zero_le_one $ by grind) $ by grind [tent]

def embZ : 𝓞 E →ₗ[ℤ] mixedSpace E :=
  ((mixedEmbedding E).comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap

abbrev ubas (E) [Field E] [NumberField E] :=
  (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)

section
variable (x : mixedSpace E)

def ucoord (i : Fin (rank E)) := (ubas E).repr (logMap x) i

def uphi := if mN x = 0 then 0 else Tent (ucoord x)

def rsgn : ℤ :=
  ∏ w, if 0 ≤ fst x w then 1 else -1

theorem uphi_nonneg : 0 ≤ uphi x := by
  unfold uphi
  split_ifs
  rfl
  exact prod_nonneg fun _ _ ↦ le_max_left _ _
theorem uphi_le_one : uphi x ≤ 1 := by
  unfold uphi
  split_ifs
  exact zero_le_one
  exact prod_le_one₀ (fun _ _ ↦ le_max_left _ _) fun _ _ ↦ max_le zero_le_one $ by grind

theorem hasSum_uphi_unit_smul (hx : mN x ≠ 0) :
    HasSum (fun u : (𝓞 E)ˣ ↦ uphi (u • x)) (rN (torsionOrder E)) := by
  let U := (𝓞 E)ˣ
  let Z := Fin (rank E) → ℤ
  let e : torsion E × Z → U | ⟨t, n⟩ => t * ∏ i, fundSystem E i ^ n i
  let eq := ofBijective e ⟨fun p q h ↦ (exist_unique_eq_mul_prod E $ e p).unique rfl h,
    fun u ↦ (exist_unique_eq_mul_prod E u).exists.imp fun _ ↦ sy⟩
  rw [← eq.hasSum_iff, show (fun u ↦ uphi $ u • x) ∘ eq = fun p : torsion E × Z ↦ Tent fun i ↦ ucoord x i + p.2 i from funext fun ⟨t, n⟩ ↦ by
    simp only [Function.comp_apply, uphi, U, norm_unit_smul, hx, ↓reduceIte]
    refine congrArg Tent $ funext fun i ↦ ?_
    rw [ucoord, show eq (t, n) • x = (t : U) • ((∏ i, fundSystem E i ^ n i : U) • x) from mul_smul _ _ _, logMap_torsion_smul _ t.2, logMap_unit_smul _ hx, ofMul_prod, map_sum, map_add]
    simp_rw [ofMul_zpow, map_zsmul, logEmbedding_fundSystem, ← cast_smul_eq_zsmul ℝ, map_sum]
    simp [ucoord, Finsupp.single_apply, add_comm]]
  let := ofFinite $ torsion E
  let y := ucoord x
  let F i : Finset ℤ := {-⌊y i⌋, -⌊y i⌋ - 1}
  have ht : HasSum (fun n : Z ↦ Tent fun i ↦ y i + n i) 1 := by
    rw [← prod_eq_one (s := univ) fun i _ ↦ show ∑ n ∈ F i, tent (y i + n) = 1 by
      rw [sum_pair $ by omega]
      grind [tent, floor_le $ y i, lt_floor_add_one $ y i], prod_univ_sum]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ by
      obtain ⟨i, hi⟩ := by simpa [Z, F] using hn
      refine prod_eq_zero (mem_univ i) ?_
      have : (n i : ℝ) ≤ -⌊y i⌋ - 2 ∨ -⌊y i⌋ + 1 ≤ (n i : ℝ) := by exact_mod_cast (by omega)
      grind [tent, floor_le $ y i, lt_floor_add_one $ y i]
  simpa [torsionOrder] using (hasSum_fintype fun _ : torsion E ↦ (1 : ℝ)).mul ht
    (mul_of_nonneg .of_finite ht.summable (fun _ ↦ zero_le_one) fun _ ↦ prod_nonneg fun _ _ ↦ le_max_left _ _)
end

def Gs (s : ℝ) (x : mixedSpace E) : ℂ :=
  chi (rsgn x : ZMod l) * ↑(uphi x * mN x ^ (-s))

lemma log_norm_eq {z : mixedSpace E} (hz : ∀ w, normAtPlace w z ≠ 0) :
    log (mN z) = ∑ w, rN (mult w) * log (normAtPlace w z) := by
  rw [mixedEmbedding.norm_apply, log_prod fun w _ ↦ pow_ne_zero _ (hz w)]
  simp_rw [Real.log_pow]

lemma supp_bound :
    ∃ c0 > 0, ∀ (x : mixedSpace E), uphi x ≠ 0 → ∀ w, c0 * norm x ≤ normAtPlace w x := by
  let B := ∑ i, ‖ubas E i‖
  let C := card (InfinitePlace E) * B
  refine ⟨exp $ -(2 * C), exp_pos _, fun x hx w ↦ ?_⟩
  have hN : mN x ≠ 0 := fun h ↦ hx $ by simp [uphi, h]
  have hc i : |ucoord x i| < 1 := mp not_le fun h' ↦ hx $ by
    simp [uphi, hN]
    exact prod_eq_zero (mem_univ i) $ max_eq_left $ by linarith
  have hB v : |logMap x v| ≤ B := by
    grw [← norm_eq_abs, norm_le_pi_norm (logMap x) v, ← (ubas E).sum_repr $ logMap x, norm_sum_le]
    exact sum_le_sum fun i _ ↦ by
      rw [_root_.norm_smul, norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc i).le
  have hpos w := lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hN w).symm
  let D w := log (normAtPlace w x) - log (mN x) * inv (rN $ finrank ℚ E)
  have hD0 : ∑ w, ↑(mult w) * D w = 0 := by
    simp_rw [D, mul_sub, sum_sub_distrib, ← log_norm_eq fun w ↦ ne_of_gt $ hpos w, ← sum_mul]
    rw [← Nat.cast_sum, sum_mult_eq]
    have : (finrank ℚ E : ℝ) ≠ 0 := mpr cast_ne_zero finrank_pos.ne'
    grind
  have hD w : |D w| ≤ C := by
    suffices key : |↑(mult w) * D w| ≤ C by
      have := one_le_mult (w := w)
      rw [abs_mul, abs_of_pos $ by linarith] at key
      nlinarith [abs_nonneg $ D w]
    by_cases hw : w = w₀
    · subst hw
      rw [sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hD0
      grw [hD0, abs_neg, abs_sum_le_sum_abs]
      refine le_trans (sum_le_sum fun v _ ↦ hB v) $ by
        simp only [sum_const, nsmul_eq_mul, C]
        gcongr
        exact card_subtype_le _
    exact le_trans (hB ⟨w, hw⟩) $ le_mul_of_one_le_left (by positivity) $ by exact_mod_cast Fintype.card_pos
  obtain ⟨w', -, hw'⟩ := exists_mem_eq_sup' univ_nonempty (normAtPlace · x)
  rw [norm_eq_sup'_normAtPlace, hw', ← exp_log $ hpos w', ← exp_add, ← exp_log $ hpos w]
  exact mpr exp_le_exp $ by grind

theorem gs_diff_bound (B : ℝ) :
    ∃ R0 C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc 1 2, ∀ x h : mixedSpace E, norm h ≤ B → R0 ≤ norm x →
      ‖Gs chi s (x + h) - Gs chi s x‖ ≤ C * norm x ^ (-rN (finrank ℚ E) - 1) := by
  obtain ⟨c0, hc0, hsupp⟩ := supp_bound (E := E)
  set n := finrank ℚ E
  set d := rN n
  have hd0 : 0 < d := mpr cast_pos finrank_pos
  let clm i := LinearMap.toContinuousLinearMap $ (ubas E).coord i
  set A := ∑ i, ‖clm i‖
  set B' := max B 1
  have hB := le_max_left B 1
  have : 1 ≤ B' := le_max_right _ _
  set m := (2 / c0) ^ n
  let L := (A * 8 + 4 * d) * B' / c0 * m
  have hL0 : 0 ≤ L := by positivity
  let R1 := max (2 * B' / c0) 1
  have : 1 ≤ R1 := le_max_right _ _
  have hscale s (hs : s ∈ Icc 1 2) (y k : mixedSpace E) (hyu : uphi y ≠ 0) (hk : norm k ≤ B') (hy : R1 ≤ norm y) :
      ‖Gs chi s (y + k) - Gs chi s y‖ ≤ L * norm y ^ (-d - 1) := by
    set y' := y + k
    set t := norm y
    have ht0 : 0 < t := by linarith
    set c2 := c0 / 2 * t with hc2
    have : B' ≤ c2 := by linarith [mp (div_le_iff₀ hc0) $ le_trans (le_max_left _ _) hy]
    have hw_y := hsupp y hyu
    have hw_le w (z : mixedSpace E) := norm_eq_sup'_normAtPlace z ▸ le_sup' (normAtPlace · z) (mem_univ w)
    have hw_diff w : |normAtPlace w y' - normAtPlace w y| ≤ B' :=
      mpr abs_le ⟨by linarith [add_neg_cancel_right y k ▸ normAtPlace_add_le w y' (-k), normAtPlace_neg w k, hw_le w k],
        by linarith [normAtPlace_add_le w y k, hw_le w k]⟩
    have hw_y' w : c2 ≤ normAtPlace w y' := by grind
    have hrsgn : rsgn y' = rsgn y := prod_congr rfl fun w _ ↦ if_congr (by
      have h1 := le_trans (hw_le w k) hk
      have h2 := hw_y w
      simp [normAtPlace_apply_of_isReal w.2] at h1 h2
      rw [fst_add, Pi.add_apply]
      grind) rfl rfl
    set ep := B' / c2
    have hlog_w w : |log (normAtPlace w y') - log (normAtPlace w y)| ≤ ep := by
      have h := (convex_Ici c2).norm_image_sub_le_of_norm_deriv_le (f := log) (C := inv c2)
        (fun x (hx : c2 ≤ x) ↦ differentiableAt_log $ by linarith)
        (fun x (hx : c2 ≤ x) ↦ by
          rw [Real.deriv_log, norm_eq_abs, abs_of_pos $ mpr inv_pos $ by linarith]
          exact inv_anti₀ (by linarith) hx)
        (show c2 ≤ normAtPlace w y by linarith [hw_y w]) $ hw_y' w
      simp_rw [norm_eq_abs] at h
      grw [hw_diff w] at h
      exact h.trans_eq $ by ring
    have hlog_N : |log (mN y') - log (mN y)| ≤ d * ep := by
      rw [log_norm_eq fun w ↦ by linarith [hw_y' w], log_norm_eq fun w ↦ by linarith [hw_y w], ← sum_sub_distrib]
      grw [abs_sum_le_sum_abs]
      dsimp [d, n, rN]
      rw [← sum_mult_eq, Nat.cast_sum, sum_mul]
      refine sum_le_sum fun w _ ↦ ?_
      rw [← mul_sub, abs_mul, abs_of_nonneg $ cast_nonneg _]
      grw [hlog_w w]
    have hlogMap : ‖logMap y' - logMap y‖ ≤ 4 * ep := mpr (pi_norm_le_iff_of_nonneg $ by positivity) fun w ↦ by
      rw [Pi.sub_apply, norm_eq_abs, logMap_apply, logMap_apply, ← mul_sub, abs_mul, abs_of_nonneg $ cast_nonneg _,
        sub_sub_sub_comm, ← sub_mul]
      grw [show mult w.val ≤ 2 by grind [mult], abs_sub, hlog_w w, abs_mul, abs_of_pos $ inv_pos.mpr hd0, hlog_N]
      apply le_of_eq
      field_simp
      ring
    set M := c2 ^ n
    have hM1 : 1 ≤ M := one_le_pow₀ $ by linarith
    have hM0 := zero_lt_one.trans_le hM1
    have hpowN {z : mixedSpace E} (hz : ∀ w, c2 ≤ normAtPlace w z) : M ≤ mN z := by
      dsimp [M, n]
      rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← prod_pow_eq_pow_sum]
      exact prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦ pow_le_pow_left₀ (by linarith) (hz w) _
    have hm_y := hpowN fun w ↦ by linarith [hw_y w]
    have hm_y' := hpowN hw_y'
    have hpow_le {N : ℝ} (hN : M ≤ N) : N ^ (-s) ≤ m * t ^ (-d) :=
      ((rpow_le_rpow_of_nonpos hM0 hN $ by linarith [hl hs]).trans $
        rpow_le_rpow_of_exponent_le hM1 (by linarith [hl hs] : -s ≤ -1)).trans_eq $ by
          dsimp [M, m, c2]
          rw [rpow_neg_one, mul_pow, mul_inv, ← inv_pow, inv_div, rpow_neg ht0.le, rpow_natCast]
    have hexp := (convex_Ici $ log M).norm_image_sub_le_of_norm_deriv_le (f := fun u ↦ exp $ -s * u) (C := m * t ^ (-d) * 2)
      (fun _ _ ↦ by fun_prop)
      (fun u (hu : log M ≤ u) ↦ by
        rw [((hasDerivAt_id' u).const_mul $ -s).exp.deriv, norm_eq_abs, abs_mul, mul_one, abs_neg,
          abs_of_pos $ exp_pos _, abs_of_pos $ by linarith [hl hs]]
        grw [hr hs, show -s * u ≤ log M * -s by nlinarith [hl hs], ← rpow_def_of_pos hM0, hpow_le le_rfl])
      (log_le_log hM0 hm_y) $ log_le_log hM0 hm_y'
    simp_rw [norm_eq_abs, mul_comm $ -s, ← rpow_def_of_pos $ hM0.trans_le hm_y',
      ← rpow_def_of_pos $ hM0.trans_le hm_y] at hexp
    have huphi : |uphi y' - uphi y| ≤ A * (4 * ep) := by
      simp [uphi, ne_of_gt $ hM0.trans_le hm_y', ne_of_gt $ hM0.trans_le hm_y]
      grw [abs_Tent_sub]
      rw [sum_mul]
      refine sum_le_sum fun i _ ↦ ?_
      grw [← hlogMap]
      simpa [ucoord, clm, map_sub] using (clm i).le_opNorm $ logMap y' - logMap y
    unfold Gs
    rw [hrsgn, ← mul_sub, norm_mul, ← ofReal_sub, Complex.norm_real, norm_eq_abs]
    grw [chi.norm_le_one]
    rw [msm]
    have := rpow_nonneg (hM0.le.trans hm_y) $ -s
    grw [abs_add_le, abs_mul, abs_mul, abs_of_nonneg this, abs_of_nonneg $ uphi_nonneg y', huphi, uphi_le_one y', hexp, hlog_N, hpow_le hm_y]
    apply le_of_eq
    rw [rpow_sub ht0, rpow_one]
    ring
  refine ⟨2 * R1 + 2 * B', L * 2 ^ (d + 1), by positivity, fun s hs x h hh hx ↦ ?_⟩
  by_cases h1 : uphi x ≠ 0
  · grw [hscale s hs x h h1 (le_trans hh hB) $ by linarith]
    gcongr
    exact le_mul_of_one_le_right hL0 $ one_le_rpow one_le_two $ by linarith
  by_cases h2 : uphi (x + h) ≠ 0
  · have hy : norm x / 2 ≤ norm (x + h) := by
      linarith [add_sub_cancel_right x h ▸ norm_sub_le (x + h) h]
    have hc := hscale s hs (x + h) (-h) h2 (sy (norm_neg h) ▸ le_trans hh hB) $ by linarith
    rw [add_neg_cancel_right, norm_sub_rev] at hc
    grw [hc, rpow_le_rpow_of_nonpos (by linarith) hy $ by linarith]
    apply le_of_eq
    rw [div_rpow (by linarith) zero_le_two, div_eq_mul_inv, ← rpow_neg zero_le_two]
    ring_nf
  simp [Gs, mp not_not h1, mp not_not h2]
  positivity

lemma norm_embZ (al : 𝓞 E) : mN (embZ al) = |(norm ℤ al : ℝ)| := by
  change mN (mixedEmbedding E al) = _
  rw [norm_eq_norm, ← coe_norm_int]
  simp_all

lemma rsgn_mul_norm (al : 𝓞 E) : rsgn (embZ al) * norm ℤ al = |norm ℤ al| := by
  set a := al.val
  have hflt w :
      (univ.filter fun ph : E →+* ℂ ↦ InfinitePlace.mk ph = w) = {w.embedding, conjugate w.embedding} := by
    ext ph
    simp
    nth_rw 1 [← mk_embedding w]
    rw [mk_eq_iff, conjugate, star_involutive.eq_iff]
  have hN : norm ℤ al =
      (∏ w : {w : InfinitePlace E // w.IsReal}, (mixedEmbedding E a).fst w) *
        ∏ w : {w : InfinitePlace E // w.IsComplex}, w.val a ^ 2 := by
    apply ofReal_injective
    have h := norm_eq_prod_embeddings ℚ ℂ a
    rw [← prod_equiv (equivRatAlgHom E ℂ) (· a) (· a) fun _ ↦ rfl,
      ← prod_fiberwise univ InfinitePlace.mk (· a),
      prod_eq_prod_mul_prod, eq_ratCast, ← coe_norm_int] at h
    push_cast at h ⊢
    rw [h]
    congr 1
    · refine prod_congr rfl fun ⟨w, hw⟩ _ ↦ ?_
      simp [hflt, isReal_iff.mp $ isReal_iff.mp hw]
    · refine prod_congr rfl fun ⟨w, hw⟩ _ ↦ ?_
      rw [hflt, prod_pair fun h' ↦ mpr not_isReal_iff_isComplex hw $ mpr isReal_iff $ mpr ComplexEmbedding.isReal_iff $ sy h',
        conjugate_coe_eq, mul_conj, ← Complex.sq_norm, norm_embedding_eq]
      simp_all
  apply cast_injective (α := ℝ)
  push_cast
  rw [hN, rsgn, Int.cast_prod, ← mul_assoc, ← prod_mul_distrib, abs_mul,
    abs_prod, abs_of_nonneg $ prod_nonneg fun _ _ ↦ sq_nonneg _]
  congr 1
  refine prod_congr rfl fun w _ ↦ ?_
  rw [show fst (embZ al) w = (mixedEmbedding E a).fst w from rfl]
  split_ifs <;> push_cast <;> grind

def gfun (C : Idl E) (s : ℝ) (a : Idl E) :=
  cf chi s a - ↑(absNorm C) * {a : Idl E | C ∣ a}.indicator (cf chi s) a

lemma exists_class_cont [Fact (Pr l)] (B C : Idl E)
    (hB0 : B ≠ ⊥) (hC0 : C ≠ ⊥) (hcop : Coprime C.absNorm (absNorm B * l)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc 1 2, Summable (gfun chi C s) →
      (∑' a, {a | a ≠ ⊥ ∧ IsPrincipal (a * B)}.indicator (gfun chi C s) a) = F s := by
  set nB := absNorm B
  set nC := absNorm C
  have hb := aN0 hB0
  set m := nB * l
  set I := span {(m : 𝓞 E)} * B
  have hIC : IsCoprime I C := mpr isCoprime_iff_exists $ by
    obtain ⟨u, v, huv⟩ := mpr isCoprime_iff_coprime $ hcop.mul_right $ hcop.coprime_dvd_right $ dvd_mul_right _ _
    exact ⟨v * (m * nB), I.mul_mem_left _ $ mul_mem_mul (mem_span_singleton_self _) $ absNorm_mem B,
      u * nC, C.mul_mem_left _ $ absNorm_mem C, by
        norm_cast
        linear_combination huv⟩
  have hI0 := mul_ne_zero (mpr span_singleton_eq_bot.not (by exact_mod_cast mul_ne_zero hb (fo : Pr l).ne_zero : (m : 𝓞 E) ≠ 0)) hB0
  let IC := I * C
  let Q := 𝓞 E ⧸ IC
  let := @ofFinite _ $ finiteQuotientOfFreeOfNeBot IC $ mul_ne_zero hI0 hC0
  let := @ofFinite _ $ finiteQuotientOfFreeOfNeBot I hI0
  let := @ofFinite _ $ finiteQuotientOfFreeOfNeBot C hC0
  let mk := Ideal.Quotient.mk IC
  let eqv := quotientMulEquivQuotientProd I C hIC
  let f a : ℂ := if a ∈ B then chi ↑(norm ℤ a / zN nB) else 0
  have hfper a a' (h : a - a' ∈ I) : f a = f a' := by
    dsimp [f]
    by_cases ha : a ∈ B
    · have ha' : a' ∈ B := by simpa using sub_mem ha $ mul_le_right h
      simp [ha, ha']
      congr 1
      rw [intCast_eq_intCast_iff]
      refine ModEq.mul_left_cancel' (mpr cast_ne_zero hb) ?_
      rw [Int.mul_ediv_cancel' $ absNorm_dvd_norm_of_mem ha, Int.mul_ediv_cancel' $ absNorm_dvd_norm_of_mem ha']
      refine mp (intCast_eq_intCast_iff _ _ m) ?_
      obtain ⟨be, hbe⟩ := mp mem_span_singleton $ mul_le_left h
      simp_rw [norm_eq_matrix_det $ Free.chooseBasis ℤ $ 𝓞 E]
      rw [eq_add_of_sub_eq hbe]
      simp_rw [← Int.coe_castRingHom, RingHom.map_det]
      congr 1
      ext i j
      simp [map_add, map_mul]
    simp [ha, show a' ∉ B from fun ha' ↦ ha $ by simpa using add_mem (mul_le_right h) ha']
  have hm (mu : IC) (y : Q) : mk (mu + out y) = y := by simp [mk, mpr eq_zero_iff_mem mu.2]
  let e : IC × Q ≃ 𝓞 E :=
    ⟨fun ⟨mu, y⟩ ↦ mu + out y,
     fun a ↦ (⟨a - out (mk a), by simp [mk, ← eq_zero_iff_mem]⟩, mk a),
     fun ⟨mu, y⟩ ↦ Prod.ext (sext (by simp [hm])) (hm mu y),
     fun a ↦ sub_add_cancel _ _⟩
  let cZ a := f a * (1 - nC * if a ∈ C then 1 else 0)
  let cQ (y : Q) := f (out (eqv y).1) * (1 - nC * if (eqv y).2 = 0 then 1 else 0)
  have hcQ a : cQ (mk a) = cZ a := by
    simp [cQ, cZ, eqv, mk, IC, eq_zero_iff_mem, hfper _ a $ mp Ideal.Quotient.eq $ out_eq _]
  have hmean : ∑ y : Q, cQ y = 0 := by
    rw [← eqv.symm.toEquiv.sum_comp, sum_prod_type]
    simp [cQ, ← mul_sum, sum_sub_distrib, nC, absNorm_apply, cardQuot_apply]
  obtain ⟨R0, C0, hC0, hRC⟩ := gs_diff_bound (E := E) chi (∑ y : Q, ‖embZ (out y)‖)
  set A := ∑ y : Q, ‖cQ y‖
  set r : ℝ := -(finrank ℚ E) - 1
  set C1 := max C0 $ 2 * max R0 1 ^ (-r)
  let L0 := mixedEmbedding.integerLattice E
  let u (mu : IC)  := A * (C1 * ‖embZ mu.1‖ ^ r + if mu = 0 then 2 else 0)
  have hu  :=
    ((((summable_norm_rpow L0 r $ by
        rw [et (rank ℝ _) $ mixedEmbedding.finrank E]
        linarith).comp_injective (i := fun mu : IC ↦ (⟨embZ mu, mu, rfl⟩ : L0)) fun _ _ h ↦
      sext $ sext $ mixedEmbedding_injective E $ congrArg Subtype.val h).mul_left C1).add
      (hasSum_ite_eq 0 2).summable).mul_left A
  let F s  := ∑' mu : IC, ∑ y : Q, cQ y * (Gs chi s (embZ (mu.1 + out y)) - Gs chi s (embZ mu.1))
  have (x : mixedSpace E) : Continuous fun s ↦ Gs chi s x := by
    unfold Gs
    by_cases h : mN x = 0
    · simpa [uphi, h] using continuous_const
    exact continuous_const.mul $ continuous_ofReal.comp $ continuous_const.mul $ (continuous_const_rpow h).comp continuous_neg
  let nb : ℂ := nB
  refine ⟨fun s ↦ inv (torsionOrder E : ℂ) * nb ^ (s : ℂ) * F s,
    (continuous_const.mul $ Continuous.const_cpow continuous_ofReal $ inl $ mpr cast_ne_zero hb).continuousOn.mul $
      continuousOn_tsum (fun _ ↦ by fun_prop) hu fun mu s hs ↦ by
        set g := Gs (E := E) chi s
        have hbd al : ‖g (embZ al)‖ ≤ 1 := by
          by_cases h0 : norm ℤ al = 0
          · simp [g, Gs, uphi, norm_embZ, h0]
          have := uphi_nonneg $ embZ al
          dsimp [g, Gs]
          rw [norm_mul, norm_embZ, Complex.norm_of_nonneg $ by positivity]
          grw [chi.norm_le_one, uphi_le_one, rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast one_le_abs h0) $ by grind]
          norm_num
        set z := embZ mu.1
        grw [norm_sum_le]
        dsimp [u, A]
        rw [sum_mul]
        refine sum_le_sum fun y _ ↦ ?_
        rw [norm_mul]
        gcongr
        have h2 : ‖g (embZ (mu + out y)) - g z‖ ≤ 2 := by
          linarith [norm_sub_le (g $ embZ $ mu + out y) $ g z, hbd $ mu + out y, hbd mu]
        split_ifs with hmu
        · have : 0 ≤ C1 * norm z ^ r := by positivity
          linarith
        · rw [add_zero]
          by_cases hR : R0 ≤ norm z
          · have h1 := hRC s hs z (embZ (out y))
              (single_le_sum (f := fun y : Q ↦ ‖embZ (out y)‖) (fun _ _ ↦ norm_nonneg _) $ mem_univ y) hR
            grw [map_add embZ, h1, le_max_left C0 _]
          · dsimp [C1]
            grw [h2, ← le_max_right C0 _, ← rpow_le_rpow_of_nonpos
              (mpr norm_pos_iff fun h ↦ hmu $ by simpa [z, embZ] using h)
              (le_trans (mp not_le hR).le $ le_max_left _ _) $ by grind]
            apply le_of_eq
            rw [mul_assoc, ← rpow_add $ by positivity, neg_add_cancel, rpow_zero, mul_one],
    fun s hs hg ↦ ?_⟩
  let g := gfun chi C s
  let ph al := cZ al * Gs chi s (embZ al)
  set S := {a : Idl E | a ≠ ⊥ ∧ IsPrincipal (a * B)}
  choose gen hgen using fun a : S ↦ a.2.2.principal
  have gen_ne a : gen a ≠ 0 := fun h ↦ mul_ne_zero a.2.1 hB0 $ (hgen a).trans $ by simp [h]
  let Ps : S × (𝓞 E)ˣ → 𝓞 E | ⟨a, u⟩ => gen a * u
  have hspan (a : S) (u : (𝓞 E)ˣ) : span {Ps (a, u)} = a * B :=
    et (span_singleton_mul_right_unit u.isUnit _) $ sy $ hgen a
  have hinj : Injective Ps := fun ⟨a, u⟩ ⟨a', u'⟩ h ↦ by
    obtain rfl : a = a' := sext $ mul_right_cancel₀ hB0 $ by rw [← hspan, ← hspan, h]
    exact Prod.ext rfl $ uext $ mul_left_cancel₀ (gen_ne a) h
  let f' : S × (𝓞 E)ˣ → ℂ | ⟨a, u⟩ => ↑(uphi (u • embZ (gen a))) * g a
  have hPout : support ph ⊆ range Ps := fun al hal ↦ by
    have halb : al ∈ B := of_not_not fun h ↦ hal $ by simp [ph, cZ, f, h]
    obtain ⟨d, hd⟩ := mpr dvd_iff_le $ mpr (span_singleton_le_iff_mem _) halb
    have hdb : d * B = span {al} := by grind
    have hdS : d ∈ S := ⟨fun h ↦ hal $ by simp [show al = 0 by simpa [h] using hd, ph, Gs, uphi], ⟨al, hdb⟩⟩
    obtain ⟨u, hu⟩ := mp span_singleton_eq_span_singleton $ et (sy $ hgen ⟨d, hdS⟩) hdb
    exact ⟨(⟨d, hdS⟩, u), hu⟩
  have hPeq : ∀ p, ph (Ps p) = nb ^ (-(s : ℂ)) * f' p := fun ⟨aS, u⟩ ↦ by
    set al := Ps (aS, u)
    have hal : al ∈ B := mp (span_singleton_le_iff_mem _) $ (hspan aS u).trans_le mul_le_right
    have hN : (norm ℤ al).natAbs = absNorm aS.1 * nB := by
      rw [← absNorm_span_singleton, hspan aS u, map_mul]
    have hC : (al ∈ C) ↔ C ∣ aS := by
      rw [← span_singleton_le_iff_mem, ← dvd_iff_le, hspan,
        (hIC.of_isCoprime_of_dvd_left $ mpr dvd_iff_le mul_le_right).symm.dvd_mul_right_iff]
    simp only [ph, cZ, f, hal, ↓reduceIte, Gs, f', g, gfun, indicator_apply, mem_ofPred_eq, cf, hC, norm_embZ, ofReal_mul, ← Int.cast_abs, ← natCast_natAbs, Int.cast_natCast, hN, ← pa_cpow_eq, cast_mul, natCast_mul_natCast_cpow]
    rw [show chi (absNorm aS.1) = chi ↑(norm ℤ al / nB) * chi (rsgn $ embZ al) by
        rw [← map_mul, ← Int.cast_mul, mul_comm, ← Int.mul_ediv_assoc _ $ absNorm_dvd_norm_of_mem hal,
          rsgn_mul_norm, ← natCast_natAbs, hN, cast_mul, mul_ediv_cancel _ $ by positivity]
        simp,
      show embZ al = u • embZ (gen aS) by simp [al, Ps, embZ, unitSMul_smul, mul_comm]]
    split_ifs <;> ring
  have hw a := hasSum_uphi_unit_smul (embZ $ gen a) $ by simp [norm_embZ, gen_ne a]
  have hfs : Summable f' := .of_norm $ mpr (summable_prod_of_nonneg fun _ ↦ norm_nonneg _) $ by
    have hnfib a : HasSum (fun u ↦ ‖f' (a, u)‖) $ torsionOrder E * ‖g a‖ := by
      convert (hw a).mul_right ‖g a‖ with u
      simp [f', abs_of_nonneg $ uphi_nonneg _]
    exact ⟨fun a ↦ (hnfib a).summable,
      ((hg.norm.subtype S).mul_left _).congr fun a ↦ sy (hnfib a).tsum_eq⟩
  have hFeq : F s = ∑' al, ph al := by
    rw [← e.tsum_eq, show (fun p ↦ ph $ e p) = ph ∘ e from rfl,
      (e.summable_iff.mpr $ mp (hinj.summable_iff fun al hal ↦ mp notMem_support $ mt (@hPout al) hal) $
        (hfs.mul_left _).congr fun p ↦ sy $ hPeq p).tsum_prod]
    refine sy $ tsum_congr fun mu ↦ ?_
    rw [tsum_fintype]
    simp_rw [Function.comp_apply, ph, e, coe_fn_mk, ← hcQ, hm, mul_sub, sum_sub_distrib, ← sum_mul, hmean, zero_mul, sub_zero]
  dsimp
  rw [hFeq, ← hinj.tsum_eq hPout, tsum_congr hPeq, tsum_mul_left, hfs.tsum_prod,
    tsum_congr fun a ↦ ((mpr hasSum_ofReal $ hw a).mul_right _).tsum_eq,
    tsum_mul_left, ofReal_natCast, tsum_subtype S g, cpow_neg]
  field_simp [torsionOrder_ne_zero E, show nb ^ (s : ℂ) ≠ 0 by simp [nb, nB, hb]]
  rfl

end

section

lemma psum_orth {l : ℕ} [Fact $ Pr l] (a : UZ l) {s : ℝ}
    (hS : Summable fun q : Prm E ↦ rp s q.asIdeal) :
    ∑ chi : DC l, re (chi ((inv a : UZ l) : ZMod l) * Psum E chi s) =
      rN (l - 1) * Pcl E l ↑a s := by
  have hc : ∑ chi, chi ((inv a : UZ l) : ZMod l) * Psum E chi s =
      (totient l : ℂ) * ↑(Pcl E l a s) := by
    unfold Psum Pcl
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum fun chi _ ↦ (of_norm_bounded hS fun _ ↦ norm_cf_le chi).mul_left _, ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun q ↦ ?_
    simp_rw [cf, ← mul_assoc, ← sum_mul, ← inv_coe_unit, DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit, indicator_apply]
    split_ifs with h1 h2 h2 <;> simp_all [pa_cpow_eq, rp]
  rw [← re_sum, hc, totient_prime (fo : Pr l)]
  simp

section
variable [Fact (Pr l)] (hirr : Irreducible $ Polynomial.cyclotomic l E)
include hirr

theorem k_holds (chi : DC l) (hchi : chi ≠ 1) :
    ∃ L1 : ℂ, Tendsto (Lser E chi) nh1 (𝓝 L1) := by
  choose I hb using fun C : ClassGroup (𝓞 E) ↦ mk0_surjective C⁻¹
  let B C := (I C).val
  have hB0 C := nonZeroDivisors.ne_zero (I C).property
  let m := ∏ C, absNorm (B C)
  have ⟨q, hqcop, hqX⟩ : ∃ q : Prm E, qC q (m * l) ∧ chi (qN q) ≠ 1 := by
    have hlp : Pr l := fo
    set M := CyclotomicField l E
    have := isGalois {l} E M
    by_contra H
    push Not at H
    let eM := autEquivPow M hirr
    let Hsub := (chi.toUnitHom.comp eM.toMonoidHom).ker
    set K := fixedField Hsub
    set k := finrank E K
    have hk : 2 ≤ k := by
      have : 0 < k := finrank_pos
      have : k ≠ 1 := fun h1 ↦ hchi $ ext fun u ↦ by
        simpa [Hsub] using congrArg Units.val $ mp mem_ker $ show eM.symm u ∈ Hsub by
          rw [← fixingSubgroup_fixedField Hsub]
          simp [K, mp finrank_eq_one_iff h1]
      omega
    set S : Set (Prm E) := {q | ¬ qC q (m * l)}
    let fS := S.indicator fun _ ↦ (1 : ℝ)
    set N := ∑' q, fS q
    set B0 := peC K + k * (N + peC E)
    refine nh1_f ?_
    filter_upwards [pe_log_bdd E, pe_log_bdd K, tendsto_log_one_div_sub_one.eventually $ eventually_gt_atTop |B0|, self_mem_nhdsWithin] with s h1 h2 hlog hs1
    let OE := 𝓞 E
    let OK := 𝓞 K
    have hSE := summable_prm_rpow E hs1
    let e := sigmaFiberEquiv $ under (E := E) (E' := K)
    have hsig : Summable fun p ↦ rpq s (e p) := e.summable_iff.mpr $ summable_prm_rpow K hs1
    let g := Sᶜ.indicator $ rpq s
    have : k * ∑' q, g q ≤ PE K s := by
      rw [← tsum_mul_left, PE, ← e.tsum_eq, hsig.tsum_sigma]
      refine tlt (fun q ↦ ?_) ((hSE.indicator Sᶜ).mul_left _) (mp (summable_sigma_of_nonneg fun _ ↦ by positivity) hsig).right
      by_cases hq : q ∈ S
      simpa [g, hq] using tsum_nonneg fun _ ↦ by positivity
      simp only [g, indicator_apply, mem_compl_iff, hq]
      have hcop := mp not_not hq
      set qi := asIdeal q
      have hsplit : ∀ Q : qi.primesOver OK, ramificationIdx Q.1 OE = 1 ∧ inertiaDeg Q.1 OE = 1 ∧ absNorm Q.1 = qN q
        | ⟨Q, hQp, hQl⟩ => by
          have hQ0 := ne_bot_of_liesOver_of_ne_bot q.ne_bot Q
          obtain ⟨⟨P, hPp, hPl⟩⟩ := Q.nonempty_primesOver (S := 𝓞 M)
          have := LiesOver.trans P Q qi
          have := q.isMaximal
          have := hQp.isMaximal hQ0
          have := hPp.isMaximal $ ne_bot_of_liesOver_of_ne_bot hQ0 P
          have hz0 := zeta_spec l E M
          set zi := hz0.toInteger
          let G := Gal(M/E)
          have htau (tau : G) (n : ℕ) (h : tau • zi - zi ^ n ∈ P) :
              ((hz0.autToPow E tau : UZ l) : ZMod l) = n := by
            set k0 := (hz0.autToPow E tau : ZMod l).val
            have hp := hz0.toInteger_isPrimitiveRoot.idealQuotient_mk (I := P)
              (absNorm_eq_one_iff.not.mpr hPp.ne_top) $ (absNorm_pow_inertiaDeg qi P) ▸ (hcop.coprime_dvd_right $ dvd_mul_left l m).pow_left _
            simpa [k0] using mpr (natCast_eq_natCast_iff k0 n l) $ sy $ sy hp.eq_orderOf ▸
              mp ((mpr isOfFinOrder_iff_pow_eq_one ⟨l, hlp.pos, hp.pow_eq_one⟩).pow_eq_pow_iff_modEq (m := k0) (n := n)) $ by
              rw [← map_pow, ← map_pow, show zi ^ k0 = tau • zi from ext $ hz0.autToPow_spec E tau]
              exact sy $ mpr Ideal.Quotient.eq h
          obtain ⟨sg, hsg⟩ := exists_of_isInvariant OE G P
          have hcardE : Nat.card (OE ⧸ P.under OE) = qN q := by
            rw [← over_def P qi, qN, absNorm_apply, cardQuot_apply]
          have hsH : sg ∈ Hsub := mpr mem_ker $ uext $ by
            simpa [eM, G, htau sg (qN q) $ hcardE ▸ hsg zi] using H q hcop
          have hN := sy $ absNorm_pow_inertiaDeg qi Q
          have h2 := two_le_Nrm q
          have hf : inertiaDeg Q OE = 1 := by
            let := iqf Q
            let := ofFinite $ OK ⧸ Q
            exact le_antisymm
              (mp (Nat.pow_le_pow_iff_right h2) $ by
                rw [← hN, pow_one, absNorm_apply, cardQuot_apply, card_eq_fintype_card, ← card_univ,
                  ← X_pow_card_sub_X_natDegree_eq (OK ⧸ Q) h2]
                refine Polynomial.card_le_degree_of_subset_roots fun z _ ↦ ?_
                obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
                have hyP := hcardE ▸ hsg (algebraMap OK (𝓞 M) x)
                rw [MulSemiringAction.toAlgHom_apply, show sg • algebraMap OK (𝓞 M) x = algebraMap OK (𝓞 M) x from
                    ext $ mp (mem_fixedField_iff _ _) x.val.2 sg hsH,
                  ← map_pow, ← map_sub] at hyP
                simp [Polynomial.mem_roots $ X_pow_card_sub_X_ne_zero _ h2,
                  sy $ mp sub_eq_zero $ by simpa using mpr eq_zero_iff_mem $ (over_def P Q).ge hyP]) $
              inertiaDeg_pos Q OE
          exact ⟨eq_one_of_mul_eq_one_right $ by
            rw [← ramificationIdx_tower (R := OE) Q P, ← ramificationIdxIn_eq_ramificationIdx qi P G,
              ← card_inertia_eq_ramificationIdxIn (G := G) qi P,
              mpr (eq_bot_iff_forall $ P.inertia G) fun g hg ↦ eM.injective $
                uext $ by simpa [eM] using htau g 1 $ by simpa using hg zi,
              card_bot], hf, by rw [hN, hf, pow_one]⟩
      let := (finite_primesOver (S := OK) qi).fintype
      have hsum := sum_ramification_inertia_eq_finrank qi OK
      rw [← IsFractionRing.finrank_eq OE E OK K,
        Finset.sum_congr rfl fun Q _ ↦ show _ = 1 by simp [OE, hsplit Q],
        sum_const, card_univ, smul_eq_mul, mul_one] at hsum
      let eqv : qi.primesOver OK ≃ {P : Prm K // under P = q} :=
        ⟨fun Q ↦
          have := Q.2.2
          ⟨⟨Q.1, Q.2.1, ne_bot_of_liesOver_of_ne_bot q.ne_bot Q.1⟩, hext $ sy $ over_def Q.1 qi⟩,
         fun P ↦ ⟨asIdeal P, P.1.isPrime, ⟨sy $ congrArg asIdeal P.2⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
      rw [← eqv.tsum_eq, tsum_fintype]
      simp [rpq, rp, e, eqv, fun Q ↦ (hsplit Q).2.2, hsum, k]
    have : PE E s - ∑' q, g q ≤ N := by
      rw [PE, ← hSE.tsum_sub $ hSE.indicator Sᶜ]
      refine tlt (fun q ↦ ?_) (hSE.sub $ hSE.indicator Sᶜ) $ summable_of_hasFiniteSupport $
        (finite_not_coprime E (m * l) $ mul_ne_zero (mpr prod_ne_zero_iff fun C _ ↦ aN0 $ hB0 C) hlp.ne_zero).subset support_indicator_subset
      simp [fS, indicator_apply]
      split_ifs <;> linarith [Nrm_rpow_le_half q hs1.le]
    nlinarith [hl $ mp abs_le h1, hr $ mp abs_le h2, le_abs_self B0, abs_nonneg B0, show (2 : ℝ) ≤ k from mpr ofNat_le_cast hk]
  set c0 := asIdeal q
  have hc0 := ne_bot q
  choose F hF hFeq using fun C ↦ exists_class_cont chi (B C) c0 (hB0 C) hc0 $ hqcop.coprime_dvd_right $ 
    mul_dvd_mul_right (dvd_prod_of_mem (fun C' ↦ absNorm $ B C') $ mem_univ C) l
  let den s := 1 - ↑(absNorm c0) * cf chi s c0
  have hdenc : Continuous den := continuous_const.sub $ continuous_const.mul $ cont_cf hc0
  have hden1 : den 1 ≠ 0 := by
    dsimp [den, cf]
    rw [cpow_neg_one, mul_left_comm, mul_inv_cancel₀ $ mpr cast_ne_zero $ aN0 hc0, mul_one, sub_eq_zero]
    exact fun h ↦ hqX h.symm
  refine ⟨(∑ C, F C 1) / den 1, ((((continuousOn_finsetSum _ fun C _ ↦ hF C) 1 ⟨le_rfl, one_le_two⟩).div hdenc.continuousWithinAt hden1).mono_of_mem_nhdsWithin
    (mem_of_superset (Ioc_mem_nhdsGT one_lt_two) Ioc_subset_Icc_self)).tendsto.congr' ?_⟩
  filter_upwards [Ioc_mem_nhdsGT one_lt_two, nhdsWithin_le_nhds $ hdenc.continuousAt.eventually_ne hden1] with s hs hs0
  refine mpr (div_eq_iff hs0) $ sy ?_
  have h1 := of_norm $ (hasSum_ideal E hs.1).left.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun _ ↦ norm_cf_le chi
  have h2 := (h1.indicator {a | c0 ∣ a}).mul_left ↑(absNorm c0)
  have hg : Summable (gfun chi c0 s) := h1.sub h2
  trans ∑' a, gfun chi c0 s a
  · dsimp [gfun, Lser]
    rw [h1.tsum_sub h2, tsum_mul_left,
      ← (mul_right_injective₀ hc0).tsum_eq (f := {a | c0 ∣ a}.indicator $ cf chi s) fun a ha ↦ (support_indicator_subset ha).imp fun _ ↦ sy,
      tsum_congr fun d ↦ show {a | c0 ∣ a}.indicator (cf chi s) (c0 * d) = cf chi s c0 * cf chi s d by simp [c0, cf, natCast_mul_natCast_cpow]
                                                                                                       ring,
      tsum_mul_left]
    ring
  dsimp
  rw [← Finset.sum_congr rfl fun C _ ↦ hFeq C s hs hg, ← Summable.tsum_finsetSum fun C _ ↦ hg.indicator _]
  refine tsum_congr fun a ↦ ?_
  by_cases ha0 : a = ⊥
  · simp [ha0, gfun, cf, zero_cpow $ mpr neg_ne_zero $ mpr ofReal_ne_zero $ by linarith [hl hs]]
  have hcl C : IsPrincipal (a * B C) ↔ mk0 ⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩ = C := by
    rw [← mul_inv_eq_one, ← hb C, ← map_mul, mk0_eq_one_iff]
    rfl
  simp [ha0, indicator_apply, hcl]

theorem cyc_holds (a : UZ l) (T : Finset ℕ) :
    ∃ q : Idl E, q.IsPrime ∧ Pr q.absNorm ∧ absNorm q ∉ T ∧
      (absNorm q : ZMod l) = a := by
  by_contra hno
  simp at hno
  let OE := 𝓞 E
  let Q := Prm E
  let g (q : Q) := (if Pr (qN q) then 0 else inv (rN (qN q))) + if qN q ∈ T then 1 else 0
  have hnp : Summable fun q : Q ↦ if Pr (qN q) then 0 else inv (rN (qN q)) := by
    let pb (q : Q) := absNorm $ q.asIdeal.under ℤ
    have hpb (q : Q) := absNorm_under_prime q.asIdeal
    let B b := if Pr b then (span {zN b}).primesOver OE else ∅
    refine hl $ fibre_sum_le pb asIdeal (fun _ _ ↦ hext) B (fun n ↦ 1 / rN n ^ 2) (finrank ℚ E)
      (fun _ ↦ by split_ifs <;> positivity) (fun q ↦ ?_) (fun _ ↦ by positivity)
      (mpr summable_one_div_nat_pow one_lt_two)
      (fun q ↦ by
        simp [B]
        exact ⟨hpb q, isPrime q, liesOver_span_absNorm q.asIdeal⟩) fun b ↦ ?_
    · split_ifs with hp
      positivity
      · set qi := asIdeal q
        have : qi.LiesOver (qi.under ℤ) := ⟨rfl⟩
        have hf := absNorm_pow_inertiaDeg (qi.under ℤ) qi
        have := (hpb q).pos
        rw [one_div]
        exact inv_anti₀ (by positivity) $ by
          exact_mod_cast (Nat.pow_le_pow_right ‹_› $ lt_of_le_of_ne (inertiaDeg_pos qi ℤ)
            fun (h1 : 1 = qi.inertiaDeg ℤ) ↦ hp $ by
              rw [qN, ← hf, ← h1, pow_one]
              exact hpb q).trans_eq hf
    · by_cases hb : Pr b
      · set p := span {zN b}
        have : p.IsPrime := mpr (span_singleton_prime $ by exact_mod_cast hb.ne_zero) $ mp prime_iff_prime_int hb
        simp only [B, hb, ↓reduceIte]
        refine ⟨finite_primesOver _, ?_⟩
        let := (finite_primesOver (S := OE) p).fintype
        rw [← card_coe_set_eq, card_eq_fintype_card, ← RingOfIntegers.rank E,
          ← sum_ramification_inertia_eq_finrank p OE, Fintype.card_eq_sum_ones]
        exact sum_le_sum fun Q _ ↦ mul_pos (Q.1.ramificationIdx_pos ℤ) $ Q.1.inertiaDeg_pos ℤ
      simp [B, hb]
  have hlp : Pr l := fo
  set k := rN $ l - 1
  set M := CyclotomicField l E
  have := isGalois {l} E M
  let Sc : Set Q := {q | ¬ qC q l}
  let fB := Sc.indicator fun _ ↦ (1 : ℝ)
  have hBf : Summable fB := summable_of_hasFiniteSupport $ (finite_not_coprime E l hlp.ne_zero).subset support_indicator_subset
  set A1 := PE E 2
  set B1 := ∑' q, fB q
  set C1 := peC E + peC M + k * (A1 + B1)
  have hC1 : ∀ᶠ s in nh1, PE E s - C1 ≤ k * Pcl E l 1 s := by
    filter_upwards [self_mem_nhdsWithin, pe_log_bdd E, pe_log_bdd M] with s hs hEs hMs
    have hA := summable_prm_rpow E one_lt_two
    let S1 : Set Q := {q | (qN q : ZMod l) = 1}
    have hP1 := (summable_prm_rpow E hs).indicator S1
    let h q := S1.indicator (rpq s) q + rpq 2 q + fB q
    have key := hr $ fibre_sum_le under asIdeal (fun _ _ ↦ hext) (fun q ↦ q.asIdeal.primesOver $ 𝓞 M) (f := rpq s) h (l - 1)
      (fun _ ↦ by positivity) (fun P ↦ by
        let q := under (E := E) P
        set Pi := asIdeal P
        simp only [h, fB, Sc, S1, indicator_apply, mem_ofPred_eq]
        have : 0 ≤ rpq 2 q := by positivity
        have : 0 ≤ rpq s q := by positivity
        by_cases hc : qC q l
        · have : Pi.LiesOver q.asIdeal := ⟨rfl⟩
          have hN := absNorm_pow_inertiaDeg q.asIdeal Pi
          have := inertiaDeg_pos Pi OE
          have := two_le_Nrm q
          by_cases h1 : Pi.inertiaDeg OE = 1
          · rw [h1, pow_one] at hN
            have := P.isMaximal
            let := iqf Pi
            have hpr := (zeta_spec l E M).toInteger_isPrimitiveRoot.idealQuotient_mk
              (I := Pi) (absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) $ hN ▸ hc
            have hd := orderOf_dvd_natCard (hpr.isUnit hlp.ne_zero).unit
            rw [← (IsPrimitiveRoot.coe_units_iff.mp hpr).eq_orderOf, Nat.card_units, ← cardQuot_apply, ← absNorm_apply, ← hN] at hd
            have : (qN q : ZMod l) = 1 := by
              simpa [Nat.cast_sub (by omega : 1 ≤ qN q), sub_eq_zero] using mpr (natCast_eq_zero_iff _ _) hd
            grind
          · have : rpq s P ≤ rpq 2 q := le_trans (Nrm_rpow_le_inv P hs.le) $ by
              rw [rpq, rp, rpow_neg $ cast_nonneg _, rpow_two]
              exact inv_anti₀ (by positivity) $ by exact_mod_cast hN ▸ Nat.pow_le_pow_right (by omega : 0 < qN q) (by omega : 2 ≤ Pi.inertiaDeg OE)
            split_ifs <;> linarith
        · split_ifs <;> linarith [Nrm_rpow_le_half P hs.le]) (fun _ ↦ by
        simp [h, fB, indicator_apply]
        split_ifs <;> positivity) ((hP1.add hA).add hBf) (fun P ↦ ⟨isPrime P, ⟨rfl⟩⟩) fun q ↦ ⟨finite_primesOver _, by
          have h2 := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q.asIdeal (𝓞 M) Gal(M/E)
          rw [IsGalois.card_aut_eq_finrank, finrank M hirr, totient_prime hlp] at h2
          exact Nat.le_of_dvd (Nat.sub_pos_of_lt hlp.one_lt) ⟨_, sy h2⟩⟩
    rw [(hP1.add hA).tsum_add hBf, hP1.tsum_add hA, ← PE, ← PE, ← Pcl] at key
    grind
  let DC' := {chi : DC l // chi ≠ 1}
  have hsplit (f : DC l → ℝ) : ∑ chi : DC l, f chi = f 1 + ∑ chi : DC', f chi := by
    rw [← add_sum_erase univ f $ mem_univ 1, sum_subtype (univ.erase 1) (p := (· ≠ 1)) (fun _ ↦ by simp) f]
  choose L1 hL using fun chi : DC' ↦ k_holds hirr chi chi.2
  have hLe (chi : DC') := (hL chi).congr' $ by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sy $ exp_ab2_eq_Lser E chi.1 hs
  have hLn (chi : DC') := ((continuous_norm.tendsto $ L1 chi).comp $ hLe chi).congr fun _ ↦ norm_exp _
  have hre_sub (chi : DC l) {s} (hs : 1 < s) := hl $ mp abs_le $ le_trans (sub_re _ _ ▸ abs_re_le_norm _) $ ab2_sub_Psum E chi hs
  let C (chi : DC') := log (‖L1 chi‖ + 1) + A1
  have hup (chi : DC') : ∀ᶠ s in nh1, re (Psum E chi.1 s) ≤ C chi := by
    filter_upwards [(hLn chi).eventually $ gt_mem_nhds $ lt_add_one ‖L1 chi‖,
      self_mem_nhdsWithin] with s hs hs1
    linarith [mpr (lt_log_iff_exp_lt $ by positivity) hs, hre_sub chi hs1]
  choose B hB using fun chi : DC' ↦
    show ∃ B, ∀ᶠ s in nh1, ‖Psum E chi.1 s‖ ≤ B by
      set c0 := chi.1
      let f := ab2 E c0
      have hL0 : L1 chi ≠ 0 := fun h0 ↦ nh1_f $ by
        set M0 := C1 + (∑ chi' ∈ univ.erase chi, C chi') + A1 + 1
        filter_upwards [(hLn chi).eventually $ gt_mem_nhds $ by simpa [h0] using exp_pos $ -M0,
          mpr eventually_all hup, hC1, self_mem_nhdsWithin] with s hs0 hsup hs1 (hgt : 1 < s)
        have hS := summable_prm_rpow E hgt
        have ho := psum_orth (1 : UZ l) hS
        simp at ho
        rw [hsplit fun chi' ↦ re $ Psum E chi' s, ← add_sum_erase _ _ $ mem_univ chi] at ho
        have : re (Psum E (1 : DC l) s) ≤ PE E s :=
          le_trans (re_le_norm _) $ tsum_of_norm_bounded hS.hasSum fun _ ↦ norm_cf_le _
        linarith [mp exp_lt_exp hs0, sum_le_sum (s := univ.erase chi) fun chi' _ ↦ hsup chi', hre_sub c0 hgt]
      let L0 := cl $ L1 chi
      let g' s := Complex.exp $ f s - L0
      have hdiv : Tendsto g' nh1 (𝓝 1) := by
        simpa [g', Complex.exp_sub, L0, Complex.exp_log hL0, div_self hL0] using (hLe chi).div_const $ L1 chi
      obtain ⟨u, hu1, hu⟩ := mp mem_nhdsGT_iff_exists_Ioo_subset
        (hdiv.eventually $ ball_mem_nhds 1 $ half_pos zero_lt_one)
      have hfI : ContinuousOn f (Ioo 1 u) := by
        rintro s0 ⟨hs0, -⟩
        set a0 := (1 + s0) / 2 with ha0
        have hcf (q : Q) {s} (hs : a0 < s) :=
          le_trans (norm_cf_le c0) $ rpow_le_rpow_of_exponent_le (by exact_mod_cast le_trans one_le_two $ two_le_Nrm q) (by linarith : -s ≤ -a0)
        have h2 q {s} (hs : a0 < s) := le_trans (hcf q hs) $ Nrm_rpow_le_half q $ by linarith
        exact ((continuousOn_tsum (fun q ↦
            ((continuous_const.sub $ cont_cf q.ne_bot).continuousOn.clog fun s (hs : a0 < s) ↦
              mpr mem_slitPlane_iff $ inl $ by
                simp
                linarith [re_le_norm $ cf c0 s q.asIdeal, h2 q hs]).neg)
            ((summable_prm_rpow E $ by linarith).mul_left $ 3 / 2) fun q s (hs : a0 < s) ↦ by
              dsimp
              rw [norm_neg, sub_eq_add_neg]
              grw [norm_log_one_add_half_le_self $ by simpa using h2 q hs, norm_neg, hcf q hs]).continuousAt
          (Ioi_mem_nhds $ by linarith)).continuousWithinAt
      have h1 {s} (hs : s ∈ Ioo 1 u) : ‖g' s - 1‖ < 1 / 2 := by simpa [dist_eq_norm] using hu hs
      let d0 := 2 * π * I
      have hd0 : d0 ≠ 0 := by simp [d0, pi_ne_zero]
      obtain ⟨c, -, hc⟩ := isPreconnected_Ioo.eqOn_const_of_mapsTo
        Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range (f := fun s ↦ (f s - L0 - cl (g' s)) / d0)
        (((hfI.sub continuousOn_const).sub $ (continuous_exp.comp_continuousOn $ hfI.sub continuousOn_const).clog fun s hs ↦
          mpr mem_slitPlane_iff $ inl $ by
            change 0 < re (g' s)
            linarith [re_le_norm $ 1 - g' s, norm_sub_rev 1 $ g' s, h1 hs, sub_re 1 $ g' s, one_re]).div_const d0)
        (fun s _ ↦ by
          obtain ⟨n, hn⟩ := mp exp_eq_exp_iff_exists_int $ sy $ exp_log $ exp_ne_zero $ f s - L0
          exact ⟨n, by dsimp
                       rw [hn, add_sub_cancel_left, mul_div_cancel_right₀ _ hd0]⟩) $
        range_nonempty _
      refine ⟨norm (c * d0 + L0) + 1 + A1, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT hu1] with s hs
      have hfs : f s = c * d0 + L0 + cl (g' s) := by grind
      rw [← sub_sub_cancel (f s) $ Psum E c0 s]
      grw [norm_sub_le, ab2_sub_Psum E c0 hs.1, hfs, norm_add_le]
      linarith [add_sub_cancel 1 (g' s) ▸ norm_log_one_add_half_le_self (h1 hs).le, h1 hs]
  have : 0 < k := mpr cast_pos $ Nat.sub_pos_of_lt hlp.one_lt
  set S := ∑ chi : DC', B chi
  refine nh1_f ?_
  filter_upwards [mpr eventually_all hB, pe_log_bdd E,
    tendsto_log_one_div_sub_one.eventually $ eventually_ge_atTop $ k * ((∑' q, g q) + 1) + S + B1 + peC E,
    self_mem_nhdsWithin] with s hsB hs3b hlog (hgt : 1 < s)
  have hS := summable_prm_rpow E hgt
  have : Pcl E l a s ≤ ∑' q, g q := by
    refine tlt (fun q ↦ ?_) (hS.indicator _) $ hnp.add $ summable_of_hasFiniteSupport $
      ((T.finite_toSet.biUnion fun n _ ↦ finite_setOfPred_absNorm_eq (S := OE) n).preimage
        (f := asIdeal) fun _ _ _ _ ↦ hext).subset fun q h ↦
        mem_biUnion (of_not_not fun hc ↦ h $ by simp [show qN q ∉ T from hc]) rfl
    simp [g, indicator_apply]
    split_ifs with hc hp hT
    all_goals first | positivity | exact absurd hc $ hno q.asIdeal q.isPrime hp hT | linarith [Nrm_rpow_le_inv q hgt.le, Nrm_rpow_le_half q hgt.le]
  have h1 := psum_orth a hS
  rw [hsplit, one_apply_coe, one_mul] at h1
  have : -S ≤ ∑ chi : DC', re (chi.1 ((inv a : UZ l) : ZMod l) * Psum E chi.1 s) := by
    rw [← sum_neg_distrib]
    exact sum_le_sum fun chi _ ↦ hl $ mp abs_le $ le_trans (abs_re_le_norm _) $ by grw [norm_mul, chi.1.norm_le_one, one_mul, hsB chi]
  have : PE E s - B1 ≤ re (Psum E (1 : DC l) s) := by
    have hcs1 := of_norm_bounded hS fun _ ↦ norm_cf_le (1 : DC l)
    rw [PE, Psum, re_tsum hcs1, ← hS.tsum_sub hBf]
    refine tlt (fun q ↦ ?_) (hS.sub hBf) $ reCLM.summable hcs1
    by_cases hc : qC q l
    · simp [cf, pa_cpow_eq, fB, Sc, hc, MulChar.one_apply $ mpr (isUnit_iff_coprime _ _) hc]
    · simp [cf, fB, Sc, hc, MulChar.map_nonunit _ $ (isUnit_iff_coprime _ _).not.mpr hc]
      linarith [Nrm_rpow_le_half q hgt.le]
  nlinarith [hl $ mp abs_le hs3b]

end

end

section

open Polynomial

theorem AlpogeRHCore2.chebotarev :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
      ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
        P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P := by
  intro K _ _ _ sg T
  let OK := 𝓞 K
  let D := (discr K).natAbs
  have hN p (hp : Pr p) (hpN : D < p) (P : Ideal OK) [P.IsPrime] (hPl : P.LiesOver $ span {zN p}) :=
    mp (not_dvd_discr_iff_forall_mem K OK $ mp prime_iff_prime_int hp)
      (fun h ↦ not_dvd_of_pos_of_lt (mpr natAbs_pos $ discr_ne_zero K) hpN $ mp ofNat_dvd_left h) P inferInstance $
      by simpa [Ideal.under] using hPl.over.le $ mem_span_singleton_self $ zN p
  obtain ⟨l, hlp, hlgt, hlmod⟩ := exists_prime_gt_modEq_one (max D (T.sup id)) (orderOf_pos sg).ne'
  have hlp0 := hlp.pos
  have : Fact (Pr l) := ⟨hlp⟩
  have hirr : Irreducible (cyclotomic l K) := by
    let lZ := span {zN l}
    obtain ⟨P, hPmax, hPl⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := OK) lZ
    have := hN l hlp (by omega) P hPl
    let g := (cyclotomic l ℤ).comp (X + 1)
    have hmon : g.Monic := (cyclotomic.monic l ℤ).comp (by simpa using monic_X_add_C (1 : ℤ)) $ by simp
    let fZ := algebraMap ℤ OK
    rw [← map_cyclotomic l $ algebraMap OK K, ← Monic.irreducible_iff_irreducible_map_fraction_map $ cyclotomic.monic l OK,
      ← MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : OK)).toMulEquiv]
    simpa [algEquivAevalXAddC_apply, ← comp_eq_aeval, g, map_comp, map_cyclotomic] using
      ((hmon.map fZ).isEisensteinAt_of_mem_of_notMem hPmax.ne_top
        (fun {n} hn ↦ sy (coeff_map fZ n) ▸ hPl.over.le ((cyclotomic_comp_X_add_one_isEisensteinAt l).mem (hmon.natDegree_map fZ ▸ hn)))
        fun hl2 ↦ mpr (ramificationIdx'_ne_one_iff $ mpr map_le_iff_le_comap hPl.over.le)
          (by simpa [g, lZ, map_span, coeff_zero_eq_eval_zero, eval_comp] using hl2) $
          et (ramificationIdx'_eq_ramificationIdx lZ P $ mpr span_singleton_eq_bot.not $ mpr cast_ne_zero hlp.ne_zero) $ P.ramificationIdx_eq_one ℤ).irreducible
        inferInstance (hmon.map _).isPrimitive $ by
          simp [hmon.natDegree_map, g, natDegree_comp, natDegree_cyclotomic, totient_prime hlp]
          have := hlp.one_lt
          omega
  let M := CyclotomicField l K
  let OM := 𝓞 M
  have : IsGalois ℚ M := by
    obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
    have ⟨p, hp0, hp⟩ : ∃ p, p ≠ 0 ∧ IsSplittingField ℚ K p :=
      if h : p = 0 then ⟨1, one_ne_zero, by simp, by simpa [h] using hp.adjoin_rootSet⟩ else ⟨p, h, hp⟩
    let qX : ℚ[X] := X ^ l - 1
    have : IsSplittingField K M $ qX.map $ algebraMap ℚ K := by simpa [qX] using isSplittingField_X_pow_sub_one l K M
    have := IsSplittingField.mul (K := K) (L := M) p qX hp0 $ X_pow_sub_C_ne_zero hlp0 1
    have := Normal.of_isSplittingField (E := M) $ p * qX
    exact ⟨⟩
  set zt := zeta l K M
  have hzt := zeta_spec l K M
  have hzpow {a b : ℕ} : zt ^ a = zt ^ b ↔ (a : ZMod l) = b := by
    rw [(mpr isOfFinOrder_iff_pow_eq_one ⟨l, hlp0, hzt.pow_eq_one⟩).pow_eq_pow_iff_modEq, ← hzt.eq_orderOf, ← natCast_eq_natCast_iff]
  obtain ⟨ta, htgen⟩ := IsCyclic.exists_generator (α := UZ l)
  have hcard := (card_units_eq_totient l).trans $ totient_prime hlp
  have hta := (orderOf_eq_card_of_forall_mem_zpowers htgen).trans $ card_eq_fintype_card.trans hcard
  obtain ⟨g, hg, hgz⟩ : ∃ g : Gal(M/ℚ), g.restrictNormal K = sg ∧ g zt = zt ^ (ta : ZMod l).val := by
    obtain ⟨g0, hg0⟩ := restrictNormalHom_surjective (F := ℚ) (K₁ := K) M sg
    have hg0z := hzt.map_of_injective g0.injective
    obtain ⟨i, -, hi⟩ := hzt.eq_pow_of_pow_eq_one hg0z.pow_eq_one
    let u := unitOfCoprime i $ mp (hzt.pow_iff_coprime hlp0 i) $ hi ▸ hg0z
    let h := (autEquivPow M hirr).symm $ ta * inv u
    refine ⟨h.restrictScalars ℚ * g0, ext fun x ↦ (algebraMap K M).injective $ by
      change g0.restrictNormal K = sg at hg0
      rw [restrictNormal_commutes, AlgEquiv.mul_apply, ← restrictNormal_commutes g0 K x, hg0]
      exact h.commutes _, ?_⟩
    dsimp
    rw [← hi, map_pow, ← hzt.autToPow_spec K h,
      show hzt.autToPow K h = ta * inv u from (autEquivPow M hirr).apply_symm_apply _,
      ← pow_mul, hzpow]
    simp [show (i : ZMod l) = u from rfl, ← Units.val_mul]
  have hpow m : (g ^ m) zt = zt ^ (↑(ta ^ m) : ZMod l).val := by
    induction m with
    | zero => simp [val_one]
    | succ m ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hgz, map_pow, ih, ← pow_mul, hzpow]
      simp [pow_succ]
  have hgl : g ^ (l - 1) = 1 := by
    set gl := g ^ (l - 1)
    have hK : gl.restrictNormal K = 1 :=
      et (map_pow (restrictNormalHom K) g _) $ et (congrArg (· ^ _) hg) $
        mp orderOf_dvd_iff_pow_eq_one $ mp (modEq_iff_dvd' hlp.one_lt.le) hlmod.symm
    exact ext fun x ↦ DFunLike.congr_fun (AlgHom.ext_of_adjoin_eq_top
      (φ₁ := { toRingHom := gl.toRingHom, commutes' := fun r ↦ by simpa [hK] using sy $ restrictNormal_commutes gl K r })
      (φ₂ := AlgHom.id K M) (adjoin_primitive_root_eq_top (A := K) hzt) $ by
        rintro _ rfl
        change gl zt = zt
        simp [gl, hpow, ← hta, val_one]) x
  set E := fixedField $ zpowers g
  have hirrE : Irreducible $ cyclotomic l E := by
    have hint := IsIntegral.isIntegral (R := E) zt
    have hdeg := card_le_degree_of_subset_roots (p := (minpoly E zt).map $ algebraMap E M)
      (Z := univ.image fun u : UZ l ↦ zt ^ (u : ZMod l).val) fun z hz ↦ by
      obtain ⟨u, -, rfl⟩ := mp mem_image hz
      obtain ⟨k, rfl⟩ := mpr mem_powers_iff_mem_zpowers $ htgen u
      rw [mem_roots $ map_ne_zero $ minpoly.ne_zero hint, IsRoot, eval_map_algebraMap, ← hpow k,
        show (g ^ k) zt = (fixingSubgroupEquiv E
          ⟨g ^ k, fixingSubgroup_fixedField (zpowers g) ▸ npow_mem_zpowers g k⟩) zt from rfl,
        aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
    rw [Finset.card_image_of_injective _ fun u v huv ↦ uext $ by simpa using mp hzpow huv,
      card_univ, hcard, natDegree_map] at hdeg
    exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic l E)
      (minpoly.dvd E zt $ by simpa [← eval_map_algebraMap] using hzt.isRoot_cyclotomic hlp0) $
      by rwa [natDegree_cyclotomic, totient_prime hlp]) ▸ minpoly.irreducible hint
  obtain ⟨q, hq, hqp, hqT, hqmod⟩ := cyc_holds hirrE ta $ T ∪ range (D + 1) ∪ {l}
  simp [Finset.mem_range] at hqT
  rcases hqT with ⟨hql, hqT, hqD⟩
  set p := absNorm q with hpdef
  have := hq.isMaximal fun h ↦ hqp.ne_zero $ hpdef ▸ h ▸ absNorm_bot
  obtain ⟨P, hPmax, hPq⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := OM) q
  have hPunder := sy hPq.over
  obtain ⟨ph, hp0⟩ := exists_of_isInvariant (𝓞 E) Gal(M/E) P
  set phQ := ph.restrictScalars ℚ
  have hPZ : P.under ℤ = span {zN p} := by
    rw [← under_under (B := 𝓞 E), hPunder]
    exact sy $ (mpr (liesOver_span_iff hq.ne_top $ mp prime_iff_prime_int hqp) $ by simpa [← hpdef] using absNorm_mem q).over
  have hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hPZ, card_congr (quotientSpanNatEquivZMod p).toEquiv, card_zmod]
  have hph : IsArithFrobAt ℤ phQ P := fun x ↦ by
    rw [hcardZ, hpdef, ← hPunder, absNorm_apply, cardQuot_apply]
    exact hp0 x
  have hpg : phQ = g := by
    obtain ⟨k, hk : g ^ k = phQ⟩ := mpr mem_powers_iff_mem_zpowers $ show phQ ∈ _ by
      rw [← fixingSubgroup_fixedField $ zpowers g, IntermediateField.mem_fixingSubgroup_iff]
      exact fun x hx ↦ ph.commutes ⟨x, hx⟩
    have hp' := et (congrArg (· zt) hk) $
      et (congrArg (·.1) $ hcardZ ▸ hph.apply_of_pow_eq_one hzt.toInteger_isPrimitiveRoot.pow_eq_one fun h ↦ hql $
        mp (prime_dvd_prime_iff_eq hqp hlp) $ mp ofNat_dvd $ mp mem_span_singleton $ by simpa [Ideal.mem_comap, ← hPZ] using h) $ SubmonoidClass.coe_pow _ _
    rw [hpow, hzpow, natCast_zmod_val, hqmod] at hp'
    rw [← hk, ← pow_one g]
    exact mpr (isOfFinOrder_of_finite g).pow_eq_pow_iff_modEq $
      (hta ▸ mp (isOfFinOrder_of_finite ta).pow_eq_pow_iff_modEq $ by simpa using uext hp').of_dvd $
        orderOf_dvd_of_pow_eq_one hgl
  set Q := P.under OK
  have hQp : Q.LiesOver $ span {zN p} := ⟨sy $ et (under_under P) hPZ⟩
  refine ⟨p, hqp, hqT, Q, inferInstance, hQp, hN _ hqp (by omega) Q hQp, fun y ↦ ?_⟩
  rw [← hg, Ideal.mem_comap]
  simpa [under_under P, show algebraMap OK OM ((g.restrictNormal K) • y) = g • algebraMap OK OM y from
    ext $ restrictNormal_commutes g K (y : K)] using (hpg ▸ hph) $ algebraMap OK OM y

end

end
