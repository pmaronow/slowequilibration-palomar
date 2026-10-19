module
public import QuantitativePaper.VectorFieldRightInverse
public import QuantitativePaper.VectorFieldDerivative
public import QuantitativePaper.VectorOverlapScore
public import QuantitativePaper.VectorShiftCalculus
public import QuantitativePaper.VectorZeroOverlap

@[expose] public section

/-! The manuscript's Hessian shift identity for actual vector potentials.
The revealed Gaussian coordinates are explicitly inverted even when some
increments have zero variance. -/
noncomputable section
open Set
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem vectorEuclideanHistoryPotential_rightInverse_deriv {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t < 1) (i : Fin (k+3)) (hi : 0 < s.q i)
    (z : VectorGaussianSpace n k) (w : Field n) :
    fderiv ℝ (vectorEuclideanHistoryPotential s β t i) z
      (vectorEuclideanFieldRightInverse s β t i w)=
      inner ℝ (vectorEuclideanMagnetization s β t i z) w := by
  let F := fun p : VectorParameter n => vectorRecursion s β t p.1 (k+2-i) p.2
  let L := vectorEuclideanStateLinear (n := n) s β t i
  have hf : Differentiable ℝ F := (contDiff_vectorRecursion_joint s β t _).differentiable (by simp)
  rw [vectorEuclideanHistoryPotential_eq_comp,
    fderiv_comp z (hf (L z)) L.differentiableAt,ContinuousLinearMap.comp_apply,L.fderiv,
    vectorEuclideanStateLinear_rightInverse s β t hβ ht i hi]
  exact fderiv_vectorRecursion_field s β t (k+2-i) (L z) w

def vectorEuclideanScoreShift {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) (i : Fin (k+3)) (z : VectorGaussianSpace n k) :
    VectorGaussianSpace n k :=
  vectorEuclideanFieldRightInverse s β t i (spinVector σ-vectorEuclideanMagnetization s β t i z)

theorem vectorEuclideanOverlapScore_eq_normalizedMeanScore {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (σ : Configuration n) (i : ℕ) :
    vectorEuclideanOverlapScore s β t σ i=
      normalizedMeanScore (vectorEuclideanMagnetization s β t i) (spinVector σ) (n : ℝ) := by
  funext z
  simp only [vectorEuclideanOverlapScore,normalizedMeanScore,fieldDot_eq_inner]

theorem vectorEuclideanOverlapScore_hessian_shift {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t < 1) (σ : Configuration n)
    (i : Fin (k+3)) (hi : 0 < s.q i) (z : VectorGaussianSpace n k) :
    hessianOperator (vectorEuclideanHistoryPotential s β t i) z
      (vectorEuclideanScoreShift s β t σ i z)=
      (n : ℝ) • gradient (vectorEuclideanOverlapScore s β t σ i) z := by
  rw [vectorEuclideanOverlapScore_eq_normalizedMeanScore]
  exact normalizedMeanScore_hessian_shift _ _ _
    ((contDiff_vectorEuclideanHistoryPotential s β t i).of_le (by simp))
    ((contDiff_vectorEuclideanMagnetization s β t i).of_le (by simp))
    (vectorEuclideanHistoryPotential_rightInverse_deriv s β t hβ ht i hi)
    (spinVector σ) (n : ℝ) (by positivity) z

theorem vectorEuclideanScoreShift_zero_overlap {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) (i : Fin (k+3)) (hi : s.q i=0) (z : VectorGaussianSpace n k) :
    vectorEuclideanScoreShift s β t σ i z=0 := by
  simp [vectorEuclideanScoreShift,vectorEuclideanFieldRightInverse,hi]

theorem vectorEuclideanOverlapScore_hessian_shift_all {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t < 1)
    (σ : Configuration n) (i : Fin (k+3)) (z : VectorGaussianSpace n k) :
    hessianOperator (vectorEuclideanHistoryPotential s β t i) z
      (vectorEuclideanScoreShift s β t σ i z)=
      (n : ℝ) • gradient (vectorEuclideanOverlapScore s β t σ i) z := by
  by_cases hi : 0 < s.q i
  · exact vectorEuclideanOverlapScore_hessian_shift hn s β t hβ ht σ i hi z
  · have hi0 : s.q i=0 := le_antisymm (le_of_not_gt hi) (s.q_nonneg (by omega))
    rw [vectorEuclideanScoreShift_zero_overlap s β t σ i hi0,
      vectorEuclideanOverlapScore_zero_overlap s β t ht.le σ i hi0]
    simp [gradient_fun_const]

end QuantitativePaper
