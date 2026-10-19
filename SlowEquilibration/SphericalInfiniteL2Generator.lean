-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteL2Semigroup
public import SlowEquilibration.SphericalInfiniteGroundState
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The physical infinite Gibbs L² semigroup differentiates on every
actual C² test, by the genuine pointwise Dynkin formula and dominated
difference quotients. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal InnerProductSpace
namespace SlowEquilibration
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000



namespace SphericalC1Dynamics
open SphericalAging SphericalAging.HardSphereDynamics SphericalReversibility
open SphericalReversibility.Ito
variable {N : ℕ}

theorem expectation_zero (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (f : State N → ℝ) (x : State N) : expectation β g hg 0 f x=f x := by
  change (∫ omega,f (process β g hg x 0 omega) ∂VectorBrownian.law N)=_
  rw [integral_congr_ae ((process_zero β g hg x).mono (fun _ h => congrArg f h))]
  simp

theorem expectation_norm_le_onSphere (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (f : State N → ℝ) (C : ℝ)
    (hC : ∀ y,OnSphere y → ‖f y‖≤C) (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖expectation β g hg t f x‖≤C := by
  simpa only [expectation,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := VectorBrownian.law N)
      ((process_onSphere hN β g hg x hx).mono (fun omega h => hC _ (h t)))

theorem expectation_slope_norm_le (hN : N≠0) (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ y,OnSphere y → ‖coefficientGenerator β g f y‖≤C)
    (x : State N) (hx : OnSphere x) (r : ℝ) (hr : 0<r) :
    ‖slope (fun s : ℝ => expectation β g hg s.toNNReal f x) 0 r‖≤C := by
  have hd := expectation_dynkin hN β g hg x hx hf r.toNNReal
  rw [Real.coe_toNNReal r hr.le] at hd
  have hb : ‖∫ s in (0 : ℝ)..r,expectation β g hg s.toNNReal
      (coefficientGenerator β g f) x‖≤C*r := by
    simpa only [sub_zero,abs_of_pos hr] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
        (fun s _ => expectation_norm_le_onSphere hN β g hg _ C hC x hx s.toNNReal)
  rw [slope_def_module,sub_zero,Real.toNNReal_zero,expectation_zero,hd,add_sub_cancel_left,
    norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)).trans_eq
    (by field_simp)
end SphericalC1Dynamics

namespace SphericalInfiniteModel
open SphericalModel SphericalForm
private theorem vector_coe_congr {X : Type*} [MeasurableSpace X] {ν η : Measure X}
    (h : ν=η) (u : Lp ℝ 2 ν) (f : X → ℝ) (hu : u=ᵐ[ν] f) :
    LawTransport.vector h u=ᵐ[η] f := by cases h;exact hu

theorem literalGibbsToL2_coe (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) (f : Vector (n+1) → ℝ) (hf : Continuous f) :
    literalGibbsToL2 n μ J hJ β f hf =ᵐ[gibbsLaw (n+1) β (SphericalInfiniteModel.field μ J)] f := by
  exact vector_coe_congr (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (gibbsToL2 (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous f hf) f
    (gibbsToL2_coe (by omega) β _ _ f hf)
end SphericalInfiniteModel

private theorem lp_slope_coe {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (U : ℝ → Lp ℝ 2 ν) (f : ℝ → X → ℝ) (hu : ∀ r,U r=ᵐ[ν] f r) (r : ℝ) :
    slope U 0 r =ᵐ[ν] fun x => slope (fun s => f s x) 0 r := by
  simp only [slope_def_module,sub_zero]
  filter_upwards [Lp.coeFn_smul r⁻¹ (U r-U 0),Lp.coeFn_sub (U r) (U 0),hu r,hu 0]
    with x hsm hsub hr h0
  rw [hsm,Pi.smul_apply,hsub,Pi.sub_apply,hr,h0]

private theorem lp_derivative_lift {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] (Q : ℝ → Lp ℝ 2 ν) (V : Lp ℝ 2 ν)
    (F : ℝ → X → ℝ) (L : X → ℝ)
    (hF : ∀ r,AEStronglyMeasurable (F r) ν) (hL : AEStronglyMeasurable L ν)
    (hQ : ∀ r,Q r=ᵐ[ν] F r) (hV : V=ᵐ[ν] L) (M : ℝ) (hM : 0≤M)
    (hb : ∀ r,0<r → ∀ᵐ x ∂ν,‖slope (fun s => F s x) 0 r‖≤M ∧ ‖L x‖≤M)
    (hd : ∀ᵐ x ∂ν,HasDerivWithinAt (fun r => F r x) (L x) (Ici 0) 0) :
    HasDerivWithinAt Q V (Ici 0) 0 := by
  let e : ℝ → X → ℝ := fun r x => slope (fun s => F s x) 0 r-L x
  have hm (r : ℝ) : AEStronglyMeasurable (fun x => e r x^2) ν := by
    convert ((((hF r).sub (hF 0)).const_mul r⁻¹).sub hL).pow 2 using 1
    funext x
    simp only [e,slope_def_module,sub_zero,smul_eq_mul,Pi.sub_apply,Pi.pow_apply]
  have hbound (r : ℝ) (hr : 0<r) : ∀ᵐ x ∂ν,‖e r x^2‖≤(2*M)^2 := by
    filter_upwards [hb r hr] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have he : ‖e r x‖≤2*M := (norm_sub_le _ _).trans
      ((add_le_add hx.1 hx.2).trans_eq (by ring))
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg (e r x)) (by positivity : 0≤2*M)).mpr he
  have ht : ∀ᵐ x ∂ν,Tendsto (fun r => e r x^2) (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 0) := by
    filter_upwards [hd] with x hx
    have hh := ((hasDerivWithinAt_iff_tendsto_slope.mp hx).sub_const (L x)).pow 2
    simpa only [e,sub_self,zero_pow (by norm_num : (2 : ℕ)≠0)] using hh
  have hI : Tendsto (fun r => ∫ x,e r x^2 ∂ν) (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2*M)^2) (.of_forall hm)
      (show ∀ᶠ r in 𝓝[Ici (0 : ℝ) \ {0}] 0,∀ᵐ x ∂ν,‖e r x^2‖≤(2*M)^2 from by
        filter_upwards [show ∀ᶠ r in 𝓝[Ici (0 : ℝ) \ {0}] 0,r∈Ici (0 : ℝ) \ {0}
          from self_mem_nhdsWithin] with r hr
        exact hbound r (lt_of_le_of_ne hr.1 (Ne.symm hr.2))) (integrable_const _) ht
  have hn (r : ℝ) : ‖slope Q 0 r-V‖^2=∫ x,e r x^2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lp_slope_coe Q F hQ r,hV,Lp.coeFn_sub (slope Q 0 r) V] with x hs hv hsub
    simp only [hsub,Pi.sub_apply,hs,hv,RCLike.inner_apply,conj_trivial,e,pow_two]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun r => ‖slope Q 0 r-V‖^2) (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 0) :=
    hI.congr' (.of_forall (fun r => (hn r).symm))
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

namespace SphericalInfinitePhysical
open SphericalModel SphericalForm SphericalInfiniteModel
open SphericalAging SphericalAging.HardSphereDynamics SphericalReversibility
open SphericalReversibility.Ito
variable (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
  (hJ : J∈summableJetDisorder μ) (β : ℝ)

theorem P_C2_hasDerivWithinAt_zero_coefficient (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt
      (fun r : ℝ => P n μ J hJ β r.toNNReal (literalGibbsToL2 n μ J hJ β f hf.continuous))
      (literalGibbsToL2 n μ J hJ β (coefficientGenerator β (infiniteGradient n μ J) f)
        (SphericalC1Dynamics.Ito.generator_continuous β _ (infiniteGradient_contDiff n μ J) hf))
      (Ici 0) 0 := by
  let := literal_gibbsLaw_probability n μ β J hJ
  let g := infiniteGradient n μ J
  let hg := infiniteGradient_contDiff n μ J
  let L := coefficientGenerator β g f
  have hL : Continuous L := SphericalC1Dynamics.Ito.generator_continuous β g hg hf
  obtain ⟨M0,hM0⟩ := (physicalSphere_compact (n+1)).exists_bound_of_continuousOn hL.continuousOn
  let M : ℝ := max M0 0
  have hM : ∀ x,OnSphere x → ‖L x‖≤M := fun x hx => (hM0 x hx).trans (le_max_left _ _)
  apply lp_derivative_lift _ _ (fun r => SphericalC1Dynamics.expectation β g hg r.toNNReal f) L
    (fun r => (SphericalC1Dynamics.expectation_stronglyMeasurable β g hg r.toNNReal f
      hf.continuous.stronglyMeasurable).aestronglyMeasurable) hL.aestronglyMeasurable
    (fun r => P_ae_expectation n μ J hJ β r.toNNReal _ hf.continuous.stronglyMeasurable
      (literalGibbsToL2_coe n μ J hJ β f hf.continuous))
    (literalGibbsToL2_coe n μ J hJ β L hL) M (le_max_right _ _)
  · intro r hr
    filter_upwards [gibbsLaw_support (show 1≤n+1 by omega) β (SphericalInfiniteModel.field μ J)] with x hx
    have hxs := (onSphere_iff_norm_sq x).mpr hx
    exact ⟨SphericalC1Dynamics.expectation_slope_norm_le (by omega) β g hg f hf M hM x hxs r hr,hM x hxs⟩
  · filter_upwards [gibbsLaw_support (show 1≤n+1 by omega) β (SphericalInfiniteModel.field μ J)] with x hx
    exact SphericalC1Dynamics.expectation_hasDerivWithinAt_zero (by omega) β g hg x
      ((onSphere_iff_norm_sq x).mpr hx) hf

theorem P_C2_hasDerivWithinAt_zero_rotation (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt
      (fun r : ℝ => P n μ J hJ β r.toNNReal (literalGibbsToL2 n μ J hJ β f hf.continuous))
      (literalGibbsToL2 n μ J hJ β (rotationGenerator (n+1) β (regularAmbientField n μ J) f)
        (rotationGenerator_continuous β ((regularAmbientField_contDiff n μ J).of_le (by norm_num)) hf))
      (Ici 0) 0 := by
  apply (P_C2_hasDerivWithinAt_zero_coefficient n μ J hJ β f hf).congr_deriv
  apply Lp.ext
  filter_upwards [literalGibbsToL2_coe n μ J hJ β
      (coefficientGenerator β (infiniteGradient n μ J) f)
      (SphericalC1Dynamics.Ito.generator_continuous β _ (infiniteGradient_contDiff n μ J) hf),
    literalGibbsToL2_coe n μ J hJ β (rotationGenerator (n+1) β (regularAmbientField n μ J) f)
      (rotationGenerator_continuous β ((regularAmbientField_contDiff n μ J).of_le (by norm_num)) hf),
    gibbsLaw_support (show 1≤n+1 by omega) β (SphericalInfiniteModel.field μ J)] with x hc hr hx
  rw [hc,hr]
  exact infiniteDifferentialGenerator_eq_rotation n μ J β hf x ((onSphere_iff_norm_sq x).mpr hx)

/-- On each actual C² observable the physical right derivative is the
negative of the independently constructed literal Gibbs weak generator. -/
theorem P_C2_hasDerivWithinAt_zero (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ hd : literalGibbsToL2 n μ J hJ β f hf.continuous ∈
        (literalWeakGenerator n μ J hJ β).domain,
      HasDerivWithinAt
        (fun r : ℝ => P n μ J hJ β r.toNNReal (literalGibbsToL2 n μ J hJ β f hf.continuous))
        (-(literalWeakGenerator n μ J hJ β) ⟨literalGibbsToL2 n μ J hJ β f hf.continuous,hd⟩)
        (Ici 0) 0 := by
  obtain ⟨hd,ha⟩ := literalWeakGenerator_C2 n μ J hJ β f hf
  refine ⟨hd,?_⟩
  rw [ha,neg_one_smul,neg_neg]
  exact P_C2_hasDerivWithinAt_zero_rotation n μ J hJ β f hf

end SphericalInfinitePhysical
end SlowEquilibration
