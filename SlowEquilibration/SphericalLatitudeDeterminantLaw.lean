-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeDeterminantScaling
public import SlowEquilibration.SphericalLatitudeScorePrecision

@[expose] public section

/-! Actual full-coefficient affine-posterior determinant law, retaining the
physical GOE dimension and the exact ambient-to-inner normalization. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphereHessian
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.ConditionedDeterminantMoments
open SlowEquilibration.GOERawMoments
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeAbsoluteDet {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y : Vector (n+1))
    (J : Disorder (n+2) P) : ℝ := |(intrinsicHessian (latitudeField c J w e q) y).det|

def latitudeDeterminantScale (n : ℕ) : ℝ :=
  (((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))^(n+1)

theorem latitudeDeterminantScale_pos (n : ℕ) : 0<latitudeDeterminantScale n := by
  unfold latitudeDeterminantScale
  positivity

def latitudeNormalizedPosterior {n : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (w : Vector (n+3)) (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (q : ℝ)
    (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)) :
    Measure (Disorder (n+3) μ.maxDegree) :=
  coefficientKernel (latitudeJointCLM (centerCoefficients (mixtureCoefficients μ) Q) w e q y hy)
    (jointScoreTarget (n+1) (((n+3 : ℕ) : ℝ) • z))

instance latitudeNormalizedPosterior_probability {n : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (w : Vector (n+3)) (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (q : ℝ)
    (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)) :
    IsProbabilityMeasure (latitudeNormalizedPosterior μ Q w e q y hy z) := by
  unfold latitudeNormalizedPosterior
  infer_instance

theorem latitude_scaled_shifted_absdet (n : ℕ) {q : ℝ} (hq : |q|≤1) (k : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    |((latitudeScale (n+1) q)^2 • W-
      ((((n+3 : ℕ) : ℝ)*k)/((n+2 : ℕ) : ℝ)) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)).det|=
      latitudeDeterminantScale n*matrixAbsoluteDet n k ((1-q^2) • W) := by
  let r : ℝ := ((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)
  have hr : 0<r := by dsimp [r]; positivity
  have hm : (latitudeScale (n+1) q)^2 • W-
      ((((n+3 : ℕ) : ℝ)*k)/((n+2 : ℕ) : ℝ)) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)=
      r • ((1-q^2) • W-k • 1) := by
    rw [latitudeScale_sq hq,smul_sub,smul_smul,smul_smul]
    congr 1
    congr 1
    dsimp [r]
    ring
  rw [hm,Matrix.det_smul,Fintype.card_fin,abs_mul,abs_of_pos (pow_pos hr _),shifted_abs_det]
  rfl

/-- Exact law of the literal original-field intrinsic determinant under
every height/radial/zero-gradient posterior target. -/
theorem latitude_posterior_absDet_hasLaw {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    (w : Vector (n+3)) (hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
    (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (he : ∀ x,inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (latitudeAbsoluteDet c w e q y)
      ((goeLaw (n+1) (n+3) (latitudeCurvatureVariance c q)).map
        (fun W => latitudeDeterminantScale n*matrixAbsoluteDet n (z 1) W))
      (latitudeNormalizedPosterior μ Q w e q y hy z) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let v := Q^2*μ.xi2 Q
  have hv : 0≤v := (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)).le
  have ht : 0≤1-q^2 := by nlinarith [(abs_lt.mp hq1).1,(abs_lt.mp hq1).2]
  have hf : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => |W.det|) := by fun_prop
  have hs : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      (latitudeScale (n+1) q)^2 • W-
        ((((n+3 : ℕ) : ℝ)*z 1)/((n+2 : ℕ) : ℝ)) • 1) := by fun_prop
  have hl := center_latitude_conditioned_intrinsic_hasLaw μ hQ w hw e he hq0 hq1 y hy
    (jointScoreTarget (n+1) (((n+3 : ℕ) : ℝ) • z))
  have hl' := (hasLaw_map hf.aemeasurable).fun_comp hl
  have hz : jointScoreTarget (n+1) (((n+3 : ℕ) : ℝ) • z) (Sum.inl 1)=((n+3 : ℕ) : ℝ)*z 1 := rfl
  rw [hz,Measure.map_map hf hs] at hl'
  have hm : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => (1-q^2) • W) := by fun_prop
  have hd : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      latitudeDeterminantScale n*matrixAbsoluteDet n (z 1) W) :=
    measurable_const.mul (matrixAbsoluteDet_measurable n (z 1))
  have hv' : latitudeCurvatureVariance c q=(1-q^2)^2*v := by
    rw [latitudeCurvatureVariance,secondCovariance_center,secondCovariance_mixture]
  rw [hv',← actual_goeLaw_map_scalar n (by omega) hv ht,Measure.map_map hd hm]
  change HasLaw (fun J => |(intrinsicHessian (latitudeField c J w e q) y).det|) _ _
  simpa only [Function.comp_def,latitudeIntrinsicMatrix_det,latitude_scaled_shifted_absdet n hq1.le,
    latitudeAbsoluteDet,latitudeNormalizedPosterior,c,v,Nat.add_assoc,Nat.reduceAdd] using hl'

end
end SlowEquilibration.SphericalLatitudeChartKacRice
