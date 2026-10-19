-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianOrthogonalRegression
public import SlowEquilibration.WholeFieldRegression

@[expose] public section

/-! Orthogonal blocks of a finite Gaussian vector remain independent under
canonical coefficient regression, even when one block shifts with the target.
This is the exact measure-theoretic mechanism behind mixed latitude bank
factorization. -/

namespace SlowEquilibration.GaussianKernelOrthogonalBlocks
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel
open GaussianRegression WholeFieldRegression
open scoped RealInnerProductSpace
set_option autoImplicit false

variable {E G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

theorem stdGaussian_orthogonal_linear_independent
    (B : E →L[ℝ] G) (C : E →L[ℝ] H)
    (hBC : B.comp C.adjoint = 0) :
    IndepFun B C (stdGaussian E) := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun (B.prod C)
  apply hG.indepFun_of_covariance_inner
  intro x y
  have hB : (fun z : E => inner ℝ x (B z)) =
      fun z => inner ℝ (B.adjoint x) z := by
    funext z
    exact (B.adjoint_inner_left z x).symm
  have hC : (fun z : E => inner ℝ y (C z)) =
      fun z => inner ℝ (C.adjoint y) z := by
    funext z
    exact (C.adjoint_inner_left z y).symm
  change cov[fun z : E => inner ℝ x (B z),
    fun z : E => inner ℝ y (C z); stdGaussian E] = 0
  rw [hB,hC,← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian,innerSL_apply_apply,B.adjoint_inner_left]
  have hz : B (C.adjoint y) = 0 :=
    congrArg (fun T : H →L[ℝ] G => T y) hBC
  rw [hz,inner_zero_right]

theorem indepFun_map_of_comp {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (T : α → β) (hT : Measurable T)
    (B : β → γ) (hB : Measurable B)
    (C : β → δ) (hC : Measurable C)
    (h : IndepFun (fun x => B (T x)) (fun x => C (T x)) μ) :
    IndepFun B C (μ.map T) := by
  have hh := h.map_prod_eq_prod_map_map
    (hB.comp hT).aemeasurable (hC.comp hT).aemeasurable
  apply (indepFun_iff_map_prod_eq_prod_map_map
    hB.aemeasurable hC.aemeasurable).2
  rw [Measure.map_map (hB.prodMk hC) hT,
    Measure.map_map hB hT,Measure.map_map hC hT]
  exact hh

variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- If one Gaussian block is orthogonal both to the conditioned observer and
to a second block, then the two blocks remain independent at every fixed
posterior target. The second block may have a target-dependent mean. -/
theorem regressionKernel_orthogonal_blocks_independent
    (A : E →L[ℝ] F) (B : E →L[ℝ] G) (C : E →L[ℝ] H)
    (hCA : C.comp A.adjoint=0) (hBC : B.comp C.adjoint=0)
    (w : F) :
    IndepFun B C (GaussianRegression.regressionKernel A w) := by
  let R := GaussianRegression.residual A
  let B' := B.comp R
  let T := fun x : E => R x + GaussianRegression.lift A w
  have hAC : A.comp C.adjoint=0 :=
    orthogonal_observation_symm C A hCA
  have hClift (v : F) : C (GaussianRegression.lift A v)=0 :=
    orthogonal_observation_lift_zero C A hCA v
  have hBC' : B'.comp C.adjoint=0 := by
    apply ContinuousLinearMap.ext
    intro y
    have hACy : A (C.adjoint y)=0 :=
      congrArg (fun D : H →L[ℝ] F => D y) hAC
    have hR : R (C.adjoint y)=C.adjoint y := by
      simp [R,GaussianRegression.residual,hACy]
    change B (R (C.adjoint y))=0
    rw [hR]
    exact congrArg (fun D : H →L[ℝ] G => D y) hBC
  have hraw := stdGaussian_orthogonal_linear_independent B' C hBC'
  have hshift : IndepFun
      (fun x : E => B' x + B (GaussianRegression.lift A w)) C
      (stdGaussian E) :=
    hraw.comp (measurable_id.add_const _) measurable_id
  have hTind : IndepFun (fun x : E => B (T x))
      (fun x : E => C (T x)) (stdGaussian E) := by
    convert hshift using 1
    · funext x
      simp only [T,map_add,B',ContinuousLinearMap.comp_apply]
    · funext x
      simp only [T,map_add,hClift,add_zero]
      have hCR : C (R x)=C x := by
        change C (x-GaussianRegression.lift A (A x))=C x
        rw [map_sub,hClift,sub_zero]
      exact hCR
  exact indepFun_map_of_comp T (by fun_prop)
    B B.continuous.measurable C C.continuous.measurable hTind

/-- The same pointwise independence for the actual ordered-tensor disorder
kernel, whose coordinates are the original coefficients rather than an
abstract Gaussian substitute. -/
theorem coefficientKernel_orthogonal_blocks_independent
    {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F)
    (B : EuclideanDisorder N P →L[ℝ] G)
    (C : EuclideanDisorder N P →L[ℝ] H)
    (hCA : C.comp A.adjoint=0) (hBC : B.comp C.adjoint=0)
    (w : F) :
    IndepFun (actualObservation B) (actualObservation C)
      (coefficientKernel A w) := by
  have hBMeas : Measurable (actualObservation B) :=
    B.continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable N P))
  have hCMeas : Measurable (actualObservation C) :=
    C.continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable N P))
  have hraw := regressionKernel_orthogonal_blocks_independent A B C hCA hBC w
  have hcomp : IndepFun
      (fun g => actualObservation B (unpackCLM N P g))
      (fun g => actualObservation C (unpackCLM N P g))
      (GaussianRegression.regressionKernel A w) := by
    convert hraw using 1 <;> funext g <;> rfl
  have hmap := indepFun_map_of_comp (unpackCLM N P)
    (unpackCLM N P).continuous.measurable
    (actualObservation B) hBMeas (actualObservation C) hCMeas hcomp
  simpa only [coefficientKernel_apply] using hmap

end
end SlowEquilibration.GaussianKernelOrthogonalBlocks
