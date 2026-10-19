module
public import FourPapersCommon.MixedSignedInitialComparison
public import FourPapersCommon.MixedLocalLeftUniform
public import FourPapersCommon.MixtureMonotonicity
public import FourPapersCommon.MixedInterleavedGaps

@[expose] public section

/-! The retained signed initial field has a genuine physical-overlap gain.
The covariance curvature is evaluated at the physical first breakpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 900000

 theorem mixture_first_le_second_endpoint_mul (ξ : AdmissibleEvenMixture)
    {x q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) q) :
    ξ.first x ≤ ξ.second q * x := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ξ.first) (f' := ξ.second)
    (fun z hz => (ξ.hasDerivAt_first_unit
      ⟨by linarith [hz.1], hz.2.trans hq.2⟩).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ξ.second_nonneg z)]
      exact ξ.second_monotoneOn ⟨hz.1, hz.2.trans hq.2⟩ hq hz.2)
    (convex_Icc (0 : ℝ) q) ⟨le_rfl, hq.1⟩ hx
  rw [ξ.first_zero, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hx.1] at H
  exact (le_abs_self _).trans H

 theorem mixedSignedInitial_slope_lower_bound (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t t₀ u e : ℝ}
    (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (-s.q 1) 0) (he : 0 ≤ e) (he_small : e ≤ (1-t₀)/2)
    (hR : ξ.second (s.q 1) * section4THessianSquare (mixedClockScheme ξ s)
      (mixedBeta ξ) h 1 0 ≤ 1+e) :
    (1-t₀)/2 * (-u) ≤
      deriv (section5RetainedSignedInitialV (mixedClockScheme ξ s) (mixedBeta ξ) h
        (t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock u)))
        ((1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
        (t*((mixedBeta ξ)^2*(-ξ.clock u)))) 0-u := by
  have hv := clock_mem_signed_initial ξ s hu
  have H := section5RetainedSignedInitialV_deriv_lower_bound (mixedClockScheme ξ s)
    (mixedBeta ξ) h
    (v := t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock u)))
    (b := (1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
    (c := t*((mixedBeta ξ)^2*(-ξ.clock u)))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg _) (by linarith [hv.1])))
    (mul_nonneg (sub_nonneg.mpr (ht.2.trans ht₀.le))
      (mul_nonneg (sq_nonneg _) ((mixedClockScheme ξ s).q_nonneg (by omega))))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg _) (neg_nonneg.mpr hv.2))) (by ring)
  have hF := mixture_first_le_second_endpoint_mul ξ
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
    (show -u ∈ Icc (0 : ℝ) (s.q 1) by constructor <;> linarith [hu.1, hu.2])
  have hvar : (mixedBeta ξ)^2*(-ξ.clock u)=ξ.first (-u) := by
    rw [←clock_neg]
    rw [mixedBeta_sq, AdmissibleEvenMixture.clock]
    field_simp [ξ.variance_pos.ne']
  have hvarH : -section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 *
      (t*((mixedBeta ξ)^2*(-ξ.clock u))) =
      -section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0*t*ξ.first (-u) := by
    rw [hvar]
    ring
  rw [hvarH] at H
  have hR0 := (section4THessianSquare_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h
    (r:=1) (by omega) 0).1
  have HF := mul_le_mul_of_nonneg_left hF (mul_nonneg hR0 ht.1)
  have HC := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR ht.1)
    (neg_nonneg.mpr hu.2)
  have Hte := mul_le_of_le_one_left he (ht.2.trans ht₀.le)
  have Hcoef : (1-t₀)/2 ≤ 1-t*(1+e) := by nlinarith only [Hte, ht.2, he_small]
  have HM := mul_le_mul_of_nonneg_right Hcoef (neg_nonneg.mpr hu.2)
  nlinarith only [H, HF, HC, HM]

 theorem mixedSignedInitial_scalar_gain_bounded (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t t₀ u e : ℝ}
    (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (-s.q 1) 0) (he : 0 ≤ e) (he_small : e ≤ (1-t₀)/2)
    (hR : ξ.second (s.q 1) * section4THessianSquare (mixedClockScheme ξ s)
      (mixedBeta ξ) h 1 0 ≤ 1+e) :
    ∃ ell : ℝ, |ell| ≤ 2 ∧
      section5RetainedSignedInitialV (mixedClockScheme ξ s) (mixedBeta ξ) h
        (t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock u)))
        ((1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
        (t*((mixedBeta ξ)^2*(-ξ.clock u))) ell-ell*u ≤
      2*parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k+2) h-(1-t₀)^2/8*u^2 := by
  have HS := mixedSignedInitial_slope_lower_bound ξ s h ht ht₀ hu he he_small hR
  have hv := clock_mem_signed_initial ξ s hu
  obtain ⟨ell, hell, HL⟩ := section5RetainedSignedInitialV_lambda_gain_bounded
    (mixedClockScheme ξ s) (mixedBeta ξ) h
    (t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock u)))
    ((1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
    (t*((mixedBeta ξ)^2*(-ξ.clock u))) u (by
      rw [abs_of_nonpos hu.2]
      exact (show -u ≤ s.q 1 by linarith [hu.1]).trans (s.q_le_one (by omega)))
  have HZ := section5RetainedSignedInitialV_zero (mixedClockScheme ξ s) (mixedBeta ξ) h
    (v := t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q 1+ξ.clock u)))
    (b := (1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
    (c := t*((mixedBeta ξ)^2*(-ξ.clock u)))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg _) (by linarith [hv.1])))
    (mul_nonneg (sub_nonneg.mpr (ht.2.trans ht₀.le))
      (mul_nonneg (sq_nonneg _) ((mixedClockScheme ξ s).q_nonneg (by omega))))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg _) (neg_nonneg.mpr hv.2))) (by ring)
  rw [HZ] at HL
  have HQ := mul_self_le_mul_self
    (mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (neg_nonneg.mpr hu.2)) HS
  refine ⟨ell, hell, ?_⟩
  nlinarith only [HL, HQ]

 theorem mixed_initial_curvature_data_of_near_minimum (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) (hm : s.m 0 < s.m 1) (hq1 : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h+ε)
    (hsmall : mixedLocalLeftConstant ξ*ε^(1/6:ℝ) ≤ 1-t₀) :
    ∃ e ≥ (0:ℝ), e ≤ (1-t₀)/2 ∧
      ξ.second (s.q 1)*section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h 1 0 ≤ 1+e := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [←mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  have hη := Real.rpow_nonneg hε (1/6:ℝ)
  let e := mixedInstabilityConstant ξ*ε^(1/6:ℝ)
  have he : 0 ≤ e := mul_nonneg (mixedInstabilityConstant_nonneg ξ) hη
  have HB := mul_le_mul_of_nonneg_right (mixedLocalLeftConstant_bounds ξ).2.2 hη
  have hE : e ≤ (1-t₀)/2 := by dsimp [e]; nlinarith only [HB, hsmall, he]
  have HR := mixed_instability_bound_all_levels ξ s h ε (r:=1) le_rfl (by omega)
    (by simpa only [Nat.sub_self] using hm)
    (by simpa only [Nat.sub_self, s.q_zero] using hq1) hright hmin hnear
  refine ⟨e, he, hE, ?_⟩
  dsimp [e]
  linarith

universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
 theorem mixed_constrainedPhi_signed_initial_of_near_minimum {n k : ℕ} (hn : 0<n)
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) (hm : s.m 0<s.m 1) (hq1 : 0<s.q 1)
    (hright : s.q 1<s.q 2 ∨ s.q 1=1) {t t₀ u : ℝ}
    (ht : t∈Icc (0:ℝ) t₀) (ht₀ : t₀<1) (hu : u∈Icc (-s.q 1) 0)
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h+ε)
    (hsmall : mixedLocalLeftConstant ξ*ε^(1/6:ℝ) ≤ 1-t₀) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u ≤
      2*mixedInterpolationPsi ξ s h t-(1-t₀)^2/8*u^2 := by
  obtain ⟨e, he, hes, HR⟩ := mixed_initial_curvature_data_of_near_minimum ξ s h ε
    hm hq1 hright ht₀ hmin hnear hsmall
  obtain ⟨ell, _, HL⟩ := mixedSignedInitial_scalar_gain_bounded ξ s h ht ht₀ hu he hes HR
  have Hu : u∈Icc (-1:ℝ) 0 := ⟨by linarith [hu.1,s.q_le_one (p:=1) (by omega)],hu.2⟩
  have HH := mixedSignedInitial_constrainedPhi_le hn ξ s h sk
    ⟨ht.1, ht.2.trans ht₀.le⟩ Hu hu ell
  simp only [tangentRemainder_self, mul_zero, add_zero] at HH
  dsimp [mixedInterpolationPsi]
  linarith

end FourPapersCommon
