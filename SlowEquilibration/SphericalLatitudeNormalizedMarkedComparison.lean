-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeMarkedComparison
public import SlowEquilibration.SphericalLatitudeDeterminantLaw

@[expose] public section

/-! The genuine marked-count comparison in physical normalized score
coordinates, matching the actual posterior law and compact count estimates. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphereHessian SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphericalSequentialRegression
open scoped ENNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actual_latitude_marked_count_le_normalized_score_count {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (w : Vector (n+3)) (hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
    (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (he : ∀ x,inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (psi : Disorder (n+3) μ.maxDegree → Vector (n+2) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+3) μ.maxDegree × Vector (n+2) => psi z.1 z.2)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) (L : ℝ)
    (hpost : ∀ (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)),
      let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,ENNReal.ofReal (latitudeAbsoluteDet c w e q y J)*psi J y
        ∂latitudeNormalizedPosterior μ Q w e q y hy z)≤
      ENNReal.ofReal L*(latitudeDeterminantMean (n+1) (Q^2*μ.xi2 Q) q (((n+3 : ℕ) : ℝ)*z 1)*f z)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,actualLatitudeSphereCount c w e q psi J ∂disorderLaw (n+3) μ.maxDegree)≤
      ENNReal.ofReal L*(∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => f (actualLatitudeScore c w e q J y)) J ∂disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let fraw : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun b => f (((n+3 : ℕ) : ℝ)⁻¹ • b)
  have hm : Measurable fraw := hf.comp (by fun_prop)
  have h := actual_latitude_marked_count_le_score_count (n := n+1) (by omega) μ hQ w hw e he hq0 hq1
    psi hpsi fraw hm L
  apply h
  intro y hy b
  have hh := hpost y hy (((n+3 : ℕ) : ℝ)⁻¹ • b)
  have hN : ((n+3 : ℕ) : ℝ)≠0 := by positivity
  have heq : ((n+3 : ℕ) : ℝ) • (((n+3 : ℕ) : ℝ)⁻¹ • b)=b := by
    rw [smul_smul,mul_inv_cancel₀ hN,one_smul]
  have heq₁ : ((n+3 : ℕ) : ℝ)*((((n+3 : ℕ) : ℝ)⁻¹ • b) 1)=b 1 := by
    change ((n+3 : ℕ) : ℝ)*(((n+3 : ℕ) : ℝ)⁻¹*b 1)=b 1
    rw [← mul_assoc,mul_inv_cancel₀ hN,one_mul]
  simpa only [latitudeNormalizedPosterior,heq,heq₁,latitudeAbsoluteDet,c,fraw] using hh

end
end SlowEquilibration.SphericalLatitudeChartKacRice
