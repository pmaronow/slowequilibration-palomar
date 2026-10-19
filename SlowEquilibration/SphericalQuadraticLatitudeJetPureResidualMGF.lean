-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureOriginalConditionalPointMean
public import SlowEquilibration.SphericalQuadraticLatitudeJetPureResidualIndependence
public import SlowEquilibration.SphericalQuadraticLatitudeJetPurePairPalmLaw
public import SlowEquilibration.GaussianCoefficientKernelScalarExpIntegrable
public import SlowEquilibration.SphericalTAPPurePalmDeterminantQuadraticReduction

@[expose] public section

/-! The exact nonquadratic scalar MGF under the literal proper-pure Palm law.
The original field and its tangential quadratic jet are on the same tensor
disorder; their factorization follows from the Gaussian block independence. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open SphericalMarkedWindows SphericalPureOriginalConditionalPointMean
open SphericalTAPPurePalmDeterminantQuadraticReduction
open GaussianCoefficientKernelScalarExpIntegrable
open SphericalTwoPointCovariance ConditionedDeterminantMoments
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPCriticalAnalyticNeighborhood
open ValueTangentConditioning
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem pure_latitude_point_norm_sq {N : ℕ}
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector N)
    (hu : ‖u‖^2=(N:ℝ)) (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=(N:ℝ)) :
    ‖originalLatitudePoint a u ω‖^2=(N:ℝ) := by
  have hcross : inner ℝ u ω=0 := by rw [real_inner_comm]; exact hω
  unfold originalLatitudePoint
  rw [norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right,hcross,mul_zero,add_zero,
    hu,hωn]
  rw [Real.sq_sqrt ha]
  ring

private theorem pure_latitude_point_overlap {N : ℕ} (hN : 0 < N)
    (a : ℝ) (u ω : Vector N) (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) :
    overlap u (originalLatitudePoint a u ω)=a := by
  rw [overlap_comm]
  unfold overlap originalLatitudePoint
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,hu,hω]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mul_zero,add_zero]
  exact mul_div_cancel_right₀ a hn

theorem nonquadraticLatitudeField_physicalPurePalm_exp_integral
    {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (hμ : 3 ≤ (FiniteMixture.pure p hp alpha halpha).minDegree)
    {Q : ℝ} (hQ : 0 < Q) (a β : ℝ) (ha : 0 ≤ 1-a^2)
    (u ω : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) (hωn : ‖ω‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J))
      ∂pureLaw p hp alpha halpha Q u hu e) =
      Real.exp (((d+2:ℕ):ℝ)*
        (β*e*(a/Real.sqrt Q)^p+
          β^2/2*(sourcePureLatitudeVariance p alpha a-
            sourceQuadraticLatitudeVariance μ a))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := pureLaw p hp alpha halpha Q u hu e
  let A := valueTangentCLM c u (tangentFrame u hu)
  let B := flatNonquadraticLatitudeField μ a u ω
  let F : Disorder (d+2) μ.maxDegree → ℝ := fun J =>
    Real.exp (β*(field (mixtureCoefficients μ) J
      (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J))
  let G : Disorder (d+2) μ.maxDegree → ℝ := fun J =>
    Real.exp (β*quadraticLatitudeJet μ a u ω J)
  have hν : ν = valueConditionedLaw c u hu e :=
    pureLaw_eq_valueConditionedLaw p hp alpha halpha Q u hu e
  have hF : Integrable F ν := by
    have hh := coefficientKernel_scalar_exp_integrable A B
      (jointValueTarget (d+1) (((d+2:ℕ):ℝ)*e)) β
    change Integrable (fun J => Real.exp (β*actualObservation B J)) ν at hh
    convert hh using 1
    funext J
    change Real.exp (β*(field (mixtureCoefficients μ) J
      (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J)) =
      Real.exp (β*B (euclideanDisorder J))
    rw [flatNonquadraticLatitudeField_actual]
  have hG : Integrable G ν := by
    have hh := quadraticLatitudeJetPair_physicalPurePalm_exp_integrable
      μ hμ Q a (β/2) u hu ω ω hω hω e
    rw [hν]
    convert hh using 1
    funext J
    dsimp [G,quadraticLatitudeJetPair]
    congr 1
    ring
  have hFB : Measurable F := by
    have hm : Measurable (actualObservation B) :=
      B.continuous.measurable.comp
        ((PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Coordinate (d+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable (d+2) μ.maxDegree))
    have hsame : F = fun J => Real.exp (β*actualObservation B J) := by
      funext J
      change Real.exp (β*(field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J)) =
        Real.exp (β*B (euclideanDisorder J))
      rw [flatNonquadraticLatitudeField_actual]
    rw [hsame]
    fun_prop
  have hGB : Measurable G := by
    have hm : Measurable (actualObservation (flatQuadraticLatitudeJet μ a u ω)) :=
      (flatQuadraticLatitudeJet μ a u ω).continuous.measurable.comp
        ((PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Coordinate (d+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable (d+2) μ.maxDegree))
    have hsame : G = fun J => Real.exp
        (β*actualObservation (flatQuadraticLatitudeJet μ a u ω) J) := by
      funext J
      simp [G,actualObservation,flatQuadraticLatitudeJet_actual]
    rw [hsame]
    fun_prop
  have hIndep : IndepFun F G ν := by
    have hh := nonquadraticLatitudeField_independent_quadraticHessian_physicalPurePalm
      μ hμ Q a hQ.le ha u ω hu hω e
    rw [← hν] at hh
    let φ : ℝ → ℝ := fun x => Real.exp (β*x)
    let ψ : EuclideanSpace ℝ (Sum (Fin 1) (Fin (d+1) × Fin (d+1))) → ℝ :=
      fun x => Real.exp (β*x (Sum.inl 0))
    have hφ : Measurable φ := by fun_prop
    have hψ : Measurable ψ := by fun_prop
    have hc := hh.comp hφ hψ
    convert hc using 1
    · funext J
      simp [F,φ]
    · funext J
      simp [G,ψ,actualObservation,
        flatQuadraticHessianBlock_inl,flatQuadraticLatitudeJet_actual]
  have hprod := hIndep.integral_mul_eq_mul_integral
    hFB.aestronglyMeasurable hGB.aestronglyMeasurable
  have hpoint (J : Disorder (d+2) μ.maxDegree) :
      F J*G J=Real.exp (β*field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω)) := by
    dsimp [F,G]
    rw [←Real.exp_add]
    congr 1
    ring
  have hpointfun : (fun J => F J*G J) =
      (fun J => Real.exp (β*field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω))) := funext hpoint
  change (∫ J, F J*G J ∂ν) = (∫ J,F J ∂ν)*(∫ J,G J ∂ν) at hprod
  rw [hpointfun] at hprod
  have hY := quadraticLatitudeJetPair_physicalPurePalm_exp_integral
    μ hμ Q a (β/2) u hu ω ω hω hω e
  rw [←hν] at hY
  have hYo : ∫ J, G J ∂ν = Real.exp
      (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2) := by
    convert hY using 1
    · apply integral_congr_ae
      filter_upwards with J
      dsimp [G,quadraticLatitudeJetPair]
      congr 1
      ring
    · rw [overlap_self (by omega) ω hωn]
      congr 1
      ring
  let s := (Real.sqrt Q)^p
  have hs : s ≠ 0 := ne_of_gt (pow_pos (Real.sqrt_pos.2 hQ) _)
  have hN : (((d+2:ℕ):ℝ)) ≠ 0 := by positivity
  let H := ((d+2:ℕ):ℝ)*e/s
  have htarget : s*H/((d+2:ℕ):ℝ)=e := by
    dsimp [H]
    field_simp
  have hw := pure_latitude_point_norm_sq a ha u ω hu hω hωn
  have hr := pure_latitude_point_overlap (by omega : 0 < d+2) a u ω hu hω
  have hX := pure_original_conditioned_point_exp_mean
    (d+1) p hp alpha halpha hQ u (originalLatitudePoint a u ω)
    (by simpa only [Nat.add_assoc] using hu)
    (by simpa only [Nat.add_assoc] using hw) hr β H
  change (∫ J, Real.exp (β*field (mixtureCoefficients μ) J
      (originalLatitudePoint a u ω))
      ∂valueConditionedLaw c u hu (s*H/((d+2:ℕ):ℝ))) =
    Real.exp (β*H*a^p+((d+2:ℕ):ℝ)*β^2*
      sourcePureLatitudeVariance p alpha a/2) at hX
  rw [htarget,←hν] at hX
  rw [hX,hYo] at hprod
  have hmain : (∫ J,F J ∂ν) = Real.exp
      (β*H*a^p+((d+2:ℕ):ℝ)*β^2*
        sourcePureLatitudeVariance p alpha a/2-
        β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2) := by
    calc
      _ = ((∫ J,F J ∂ν) * Real.exp
            (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)) *
            Real.exp (-(β^2*((d+2:ℕ):ℝ)*
              sourceQuadraticLatitudeVariance μ a/2)) := by
              rw [mul_assoc,←Real.exp_add]
              simp
      _ = Real.exp (β*H*a^p+((d+2:ℕ):ℝ)*β^2*
            sourcePureLatitudeVariance p alpha a/2) *
            Real.exp (-(β^2*((d+2:ℕ):ℝ)*
              sourceQuadraticLatitudeVariance μ a/2)) := by rw [←hprod]
      _ = _ := by rw [←Real.exp_add]; congr 1
  convert hmain using 1
  congr 1
  dsimp [H,s]
  rw [div_pow]
  field_simp [hs,Real.sqrt_ne_zero'.mpr hQ]
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
