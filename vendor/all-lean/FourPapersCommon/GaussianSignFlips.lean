module
public import Lemmas.SpinGlass.gaussian_concentration
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-! Actual finite Gaussian coordinate-sign symmetries. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {ι : Type*} [Fintype ι]

def coordinateSignEquiv (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 (fun i => ε i * x i)
      invFun := fun x => WithLp.toLp 2 (fun i => ε i * x i)
      left_inv := by
        intro x
        ext i
        change ε i * (ε i * x i) = x i
        have hh : ε i ^ 2 = 1 := by nlinarith [sq_abs (ε i), hε i]
        rw [← mul_assoc, ← pow_two, hh, one_mul]
      right_inv := by
        intro x
        ext i
        change ε i * (ε i * x i) = x i
        have hh : ε i ^ 2 = 1 := by nlinarith [sq_abs (ε i), hε i]
        rw [← mul_assoc, ← pow_two, hh, one_mul]
      map_add' := by
        intro x y
        ext i
        change ε i * (x i + y i) = ε i * x i + ε i * y i
        ring
      map_smul' := by
        intro a x
        ext i
        change ε i * (a * x i) = a * (ε i * x i)
        ring }
  norm_map' := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change ‖ε i * x i‖ ^ 2 = ‖x i‖ ^ 2
    rw [norm_mul, Real.norm_eq_abs (ε i), hε i, one_mul]

def coordinateSignCLM (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (coordinateSignEquiv ε hε).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem coordinateSignCLM_apply (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1)
    (x : EuclideanSpace ℝ ι) (i : ι) : coordinateSignCLM ε hε x i = ε i * x i := rfl

theorem standardGaussianMeasure_coordinateSign_map (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    (SYK.standardGaussianMeasureOnEuclidean ι).map (coordinateSignCLM ε hε) =
      SYK.standardGaussianMeasureOnEuclidean ι := by
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [map_pi_eq_stdGaussian]
  exact stdGaussian_map (coordinateSignEquiv ε hε)

theorem measurePreserving_coordinateSign (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    MeasurePreserving (coordinateSignCLM ε hε)
      (SYK.standardGaussianMeasureOnEuclidean ι) (SYK.standardGaussianMeasureOnEuclidean ι) :=
  ⟨(coordinateSignCLM ε hε).measurable, standardGaussianMeasure_coordinateSign_map ε hε⟩

end FourPapersCommon
