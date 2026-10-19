-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianTargetIsometry
public import SlowEquilibration.SphericalPairIntrinsicKacRice
public import SlowEquilibration.PairScoreDisintegration

/-! Exact complete-tangent coordinates for the intrinsic pair Kac--Rice
observation and its canonical original-tensor zero-gradient law. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet SphericalForm
open GaussianRegression GaussianObservationCoercivity WholeFieldRegression IntrinsicHessianLaw
open IntrinsicGradientRegression SphericalSequentialRegression SphericalPairIntrinsicCoordinates ObservationTargetEquiv
open scoped RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def pairIntrinsicFrameEquiv {n : ℕ} (x y : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) :
    WithLp 2 (tangentPlane x×tangentPlane y) ≃ₗᵢ[ℝ] GradientPairSpace n :=
  (tangentBasis x hx).repr.withLpProdCongr 2 (tangentBasis y hy).repr

lemma pairGradient_eq_intrinsic_frame {n P : ℕ} (c : Degree P → ℝ)
    (x y : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) :
    pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)=
      (pairIntrinsicFrameEquiv x y hx hy : WithLp 2 (tangentPlane x×tangentPlane y) →L[ℝ] GradientPairSpace n).comp
        (pairIntrinsicGamma c x y) := by
  ext g
  change WithLp.toLp 2 (gradientCLM c x (tangentFrame x hx) g,gradientCLM c y (tangentFrame y hy) g)=_
  rw [tangentFrame_gradient_eq,tangentFrame_gradient_eq]
  rfl

/-- The actual coordinate and coordinate-free pair densities agree at the
literal zero-gradient target, using a complete genuine tangent basis. -/
theorem pairGradient_pdf_zero_eq_intrinsic {n P : ℕ} (c : Degree P → ℝ)
    (x y : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) :
    observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0=
      observationPdf (pairIntrinsicGamma c x y) 0 := by
  rw [pairGradient_eq_intrinsic_frame,observationPdf_zero_target_isometry]

/-- Full original disorder posteriors coincide at gradient zero; the frame
merely supplies coordinates in both complete tangent spaces. -/
theorem pairGradient_kernel_zero_eq_intrinsic {n P : ℕ} (c : Degree P → ℝ)
    (x y : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ))
    (hA : Surjective (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy))) :
    coefficientKernel (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0=
      coefficientKernel (pairIntrinsicGamma c x y) 0 := by
  have hIntrinsic : Surjective (pairIntrinsicGamma c x y) := by
    intro w
    obtain ⟨g,hg⟩:=hA (pairIntrinsicFrameEquiv x y hx hy w)
    refine ⟨g,(pairIntrinsicFrameEquiv x y hx hy).injective ?_⟩
    rw [pairGradient_eq_intrinsic_frame] at hg
    exact hg
  rw [pairGradient_eq_intrinsic_frame]
  let e' : WithLp 2 (tangentPlane x×tangentPlane y) ≃L[ℝ] GradientPairSpace n :=
    (pairIntrinsicFrameEquiv x y hx hy).toContinuousLinearEquiv
  have h:=coefficientKernel_target_equiv (pairIntrinsicGamma c x y) hIntrinsic e'
    (0 : WithLp 2 (tangentPlane x×tangentPlane y))
  rw [e'.map_zero] at h
  exact h

end
end SlowEquilibration.NormalizedPairObservations
