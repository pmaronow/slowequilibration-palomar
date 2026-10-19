-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeRegularDisorder
public import SlowEquilibration.SphericalPlantedShift
public import SlowEquilibration.MixtureCurvature

@[expose] public section

/-! Uniform genuine gradient bounds for the actual planted tensor
translate, on the existing exponential-probability disorder event. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory Set Metric InnerProductSpace
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem overlap_ball_abs_le {N : ℕ} (hN : 1≤N) (w : Vector N)
    (hw : ‖w‖^2=(N : ℝ)) (x : Vector N) (hx : ‖x‖≤Real.sqrt (N : ℝ)) :
    |overlap x w|≤1 := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hwn : ‖w‖=Real.sqrt (N : ℝ) := by rw [← hw,Real.sqrt_sq (norm_nonneg _)]
  rw [overlap,abs_div,abs_of_pos hNr]
  apply (div_le_one hNr).mpr
  calc
    _ ≤ ‖x‖*‖w‖ := abs_real_inner_le_norm x w
    _ ≤ Real.sqrt (N : ℝ)*Real.sqrt (N : ℝ) := by rw [hwn]; gcongr
    _ = (N : ℝ) := by rw [← pow_two,Real.sq_sqrt hNr.le]

theorem overlap_hasFDerivAt {N : ℕ} (w x : Vector N) :
    HasFDerivAt (fun z => overlap z w) ((N : ℝ)⁻¹ • innerSL ℝ w) x := by
  have h := ((innerSL ℝ w).hasFDerivAt (x := x)).const_smul ((N : ℝ)⁻¹)
  convert h using 1
  funext z
  change inner ℝ z w/(N : ℝ)=(N : ℝ)⁻¹*inner ℝ w z
  rw [real_inner_comm]
  ring

theorem plantedShift_hasFDerivAt {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (β : ℝ) (w x : Vector N) :
    HasFDerivAt (field (mixtureCoefficients μ) (plantedShift (mixtureCoefficients μ) β w))
      ((β*μ.xi1 (overlap x w)) • innerSL ℝ w) x := by
  have hR := overlap_hasFDerivAt w x
  have hd := ((μ.hasDerivAt_xi (overlap x w)).comp_hasFDerivAt x hR).const_mul (β*(N : ℝ))
  have hN0 : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hfun : field (mixtureCoefficients μ) (plantedShift (mixtureCoefficients μ) β w)=
      fun z => β*(N : ℝ)*μ.xi (overlap z w) := by
    funext z
    rw [plantedShift_field hN _ (mixtureCoefficients_nonnegative μ),covariancePolynomial_mixture]
  rw [hfun]
  simp only [Function.comp_apply,smul_smul] at hd
  have hcoef : (β*(N : ℝ))*(μ.xi1 (overlap x w)*(N : ℝ)⁻¹)=β*μ.xi1 (overlap x w) := by
    field_simp
  rw [hcoef] at hd
  exact hd

/-- The constant is independent of dimension, reference direction and
actual disorder. The event is the already proved tensor regularity event. -/
theorem exists_planted_regularDisorder_gradient_bound (μ : FiniteMixture) (β : ℝ) :
    ∃ K : ℝ,0<K ∧ ∀ (N : ℕ),2≤N → ∀ (w : Vector N),‖w‖^2=(N : ℝ) →
      ∀ (J : Disorder N μ.maxDegree),J∈regularDisorder →
      ∀ (x : Vector N),‖x‖≤Real.sqrt (N : ℝ) →
        ‖fderiv ℝ (fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β w)) x‖≤
          K*Real.sqrt (N : ℝ) := by
  have hξ : Continuous μ.xi1 := by unfold FiniteMixture.xi1; fun_prop
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn hξ.continuousOn
  let B := max M 0
  let c := mixtureCoefficients μ
  let K := derivativeConstant c+|β| *B
  have hB : 0≤B := le_max_right _ _
  have hK : 0<K := by
    dsimp only [K]
    exact add_pos_of_pos_of_nonneg (derivativeConstant_pos c) (mul_nonneg (abs_nonneg _) hB)
  refine ⟨K,hK,?_⟩
  intro N hN w hw J hJ x hx
  have hnorm : ‖w‖=Real.sqrt (N : ℝ) := by rw [← hw,Real.sqrt_sq (norm_nonneg _)]
  have hR : overlap x w∈Icc (-1 : ℝ) 1 := abs_le.mp (overlap_ball_abs_le (by omega) w hw x hx)
  have hbM : |μ.xi1 (overlap x w)|≤M := by simpa only [Real.norm_eq_abs] using hM _ hR
  have hb : |μ.xi1 (overlap x w)|≤B := hbM.trans (le_max_left _ _)
  have hshift := (plantedShift_hasFDerivAt (by omega) μ β w x).fderiv
  have hshiftbound : ‖fderiv ℝ (field c (plantedShift c β w)) x‖≤|β| *B*Real.sqrt (N : ℝ) := by
    rw [hshift,norm_smul,Real.norm_eq_abs,abs_mul,innerSL_apply_norm,hnorm]
    gcongr
  have hbase : ‖fderiv ℝ (field c J) x‖≤derivativeConstant c*Real.sqrt (N : ℝ) := by
    have hg := (field_regularDisorder_ball_bounds (by omega) c J hJ x hx).2.1
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hg
  have hfun : field c (J+plantedShift c β w)=fun z => field c J z+field c (plantedShift c β w) z := by
    funext z
    rw [← fieldCLM_apply,map_add,fieldCLM_apply,fieldCLM_apply]
  change ‖fderiv ℝ (field c (J+plantedShift c β w)) x‖≤_
  rw [hfun]
  change ‖fderiv ℝ (field c J+field c (plantedShift c β w)) x‖≤_
  rw [fderiv_add ((field_contDiff c J).differentiable (by simp) x)
    ((field_contDiff c (plantedShift c β w)).differentiable (by simp) x)]
  calc
    _ ≤ ‖fderiv ℝ (field c J) x‖+‖fderiv ℝ (field c (plantedShift c β w)) x‖ := norm_add_le _ _
    _ ≤ derivativeConstant c*Real.sqrt (N : ℝ)+|β| *B*Real.sqrt (N : ℝ) := add_le_add hbase hshiftbound
    _ = K*Real.sqrt (N : ℝ) := by dsimp only [K]; ring

end
end SlowEquilibration.SphericalModel
