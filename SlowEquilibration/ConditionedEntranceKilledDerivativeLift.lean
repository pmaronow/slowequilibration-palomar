-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledStrongContinuity
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Genuine dominated lifting of a physical pointwise core derivative
to its actual reference Hilbert space. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem lp_slope_ae {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (U : ℝ → Lp ℝ 2 ν) (f : ℝ → X → ℝ) (hu : ∀ r, U r =ᵐ[ν] f r) (r : ℝ) :
    slope U 0 r =ᵐ[ν] fun x => slope (fun s => f s x) 0 r := by
  simp only [slope_def_module,sub_zero]
  filter_upwards [Lp.coeFn_smul r⁻¹ (U r-U 0),Lp.coeFn_sub (U r) (U 0),hu r,hu 0]
    with x hsm hsub hr h0
  rw [hsm,Pi.smul_apply,hsub,Pi.sub_apply,hr,h0]

theorem lp_derivative_lift {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] (Q : ℝ → Lp ℝ 2 ν) (V : Lp ℝ 2 ν)
    (F : ℝ → X → ℝ) (L : X → ℝ)
    (hF : ∀ r, AEStronglyMeasurable (F r) ν) (hL : AEStronglyMeasurable L ν)
    (hQ : ∀ r, Q r =ᵐ[ν] F r) (hV : V =ᵐ[ν] L) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ r, 0 < r → ∀ᵐ x ∂ν, ‖slope (fun s => F s x) 0 r‖ ≤ M ∧ ‖L x‖ ≤ M)
    (hd : ∀ᵐ x ∂ν, HasDerivWithinAt (fun r => F r x) (L x) (Ici 0) 0) :
    HasDerivWithinAt Q V (Ici 0) 0 := by
  let e : ℝ → X → ℝ := fun r x => slope (fun s => F s x) 0 r-L x
  have hm (r : ℝ) : AEStronglyMeasurable (fun x => e r x^2) ν := by
    convert ((((hF r).sub (hF 0)).const_mul r⁻¹).sub hL).pow 2 using 1
    funext x
    simp only [e,slope_def_module,sub_zero,smul_eq_mul,Pi.sub_apply,Pi.pow_apply]
  have hbound (r : ℝ) (hr : 0 < r) : ∀ᵐ x ∂ν, ‖e r x^2‖ ≤ (2*M)^2 := by
    filter_upwards [hb r hr] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have he : ‖e r x‖ ≤ 2*M := (norm_sub_le _ _).trans ((add_le_add hx.1 hx.2).trans_eq (by ring))
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg (e r x)) (by positivity : 0 ≤ 2*M)).mpr he
  have ht : ∀ᵐ x ∂ν, Tendsto (fun r => e r x^2) (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 0) := by
    filter_upwards [hd] with x hx
    have hh := ((hasDerivWithinAt_iff_tendsto_slope.mp hx).sub_const (L x)).pow 2
    simpa only [e,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hh
  have hI : Tendsto (fun r => ∫ x, e r x^2 ∂ν) (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2*M)^2) (.of_forall hm)
      (show ∀ᶠ r in 𝓝[Ici (0 : ℝ) \ {0}] 0, ∀ᵐ x ∂ν, ‖e r x^2‖ ≤ (2*M)^2 from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact hbound r (lt_of_le_of_ne hr.1 (Ne.symm hr.2)))
      (integrable_const _) ht
  have hn (r : ℝ) : ‖slope Q 0 r-V‖^2 = ∫ x, e r x^2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lp_slope_ae Q F hQ r,hV,Lp.coeFn_sub (slope Q 0 r) V] with x hs hv hsub
    simp only [hsub,Pi.sub_apply,hs,hv,RCLike.inner_apply,conj_trivial,e,pow_two]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun r => ‖slope Q 0 r-V‖^2) (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 0) :=
    hI.congr' (.of_forall (fun r => (hn r).symm))
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

end SlowEquilibration.ConditionedEntrance.FeynmanKac
