module
public import QuantitativePaper.VectorConcreteShift

@[expose] public section

/-! Literal quadratic shift energy for actual vector field Hessians. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

def vectorFieldHessian {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) : Field n →L[ℝ] Field n :=
  hessianOperator (vectorRecursion s β t p j) x

theorem contDiff_vectorRecursion_field {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (vectorRecursion s β t p j) :=
  (contDiff_vectorRecursion_joint s β t j).comp (contDiff_const.prodMk contDiff_id)

theorem vectorFieldHessian_quadratic_nonneg {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x w : Field n) :
    0 ≤ inner ℝ w (vectorFieldHessian s β t p j x w) := by
  let F := fun y : VectorParameter n => vectorRecursion s β t y.1 j y.2
  have hf : ContDiff ℝ 2 F := (contDiff_vectorRecursion_joint s β t j).of_le (by simp)
  have he : (fun r : ℝ => F ((p,x)+r • ((0,w) : VectorParameter n)))=
      fun r => vectorRecursion s β t p j (x+r • w) := by
    funext r
    simp [F,Prod.smul_mk]
  rw [real_inner_comm,vectorFieldHessian,inner_hessianOperator]
  change 0 ≤ directionalHessian (vectorRecursion s β t p j) x w
  rw [directionalHessian_eq_secondDeriv_line _
    ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)),←he,
    ←directionalHessian_eq_secondDeriv_line F hf]
  exact directionalHessian_nonneg_of_convex F hf (convexOn_vectorRecursion_joint s β t j) (p,x) (0,w)

theorem vectorEuclideanScoreShift_energy_eq {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t < 1) (σ : Configuration n)
    (i : Fin (k+3)) (hi : 0 < s.q i) (z : VectorGaussianSpace n k) :
    inner ℝ (vectorEuclideanScoreShift s β t σ i z)
      (hessianOperator (vectorEuclideanHistoryPotential s β t i) z
        (vectorEuclideanScoreShift s β t σ i z))=
      inner ℝ (spinVector σ-vectorEuclideanMagnetization s β t i z)
        (vectorFieldHessian s β t (vectorEuclideanStateLinear s β t i z).1 (k+2-i)
          (vectorEuclideanStateLinear s β t i z).2
          (spinVector σ-vectorEuclideanMagnetization s β t i z)) := by
  let L := vectorEuclideanStateLinear (n := n) s β t i
  let w := spinVector σ-vectorEuclideanMagnetization s β t i z
  let v := vectorEuclideanScoreShift s β t σ i z
  have hv : L v=(0,w) := vectorEuclideanStateLinear_rightInverse s β t hβ ht i hi w
  have he : (fun r : ℝ => vectorEuclideanHistoryPotential s β t i (z+r • v))=
      fun r => vectorRecursion s β t (L z).1 (k+2-i) ((L z).2+r • w) := by
    funext r
    rw [vectorEuclideanHistoryPotential_eq_comp,Function.comp_apply]
    change vectorRecursion s β t (L (z+r • v)).1 (k+2-i) (L (z+r • v)).2=_
    rw [map_add,map_smul,hv]
    simp [Prod.smul_mk]
  conv_lhs => rw [real_inner_comm]
  conv_rhs => rw [real_inner_comm]
  rw [inner_hessianOperator,vectorFieldHessian,inner_hessianOperator]
  change directionalHessian (vectorEuclideanHistoryPotential s β t i) z v=
    directionalHessian (vectorRecursion s β t (L z).1 (k+2-i)) (L z).2 w
  rw [directionalHessian_eq_secondDeriv_line _
    ((contDiff_vectorEuclideanHistoryPotential s β t i).of_le (by simp)),he,
    ←directionalHessian_eq_secondDeriv_line _
      ((contDiff_vectorRecursion_field s β t (L z).1 (k+2-i)).of_le (by simp))]

theorem vectorEuclideanScoreShift_energy_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t < 1) (σ : Configuration n)
    (i : Fin (k+3)) (z : VectorGaussianSpace n k) :
    inner ℝ (vectorEuclideanScoreShift s β t σ i z)
      (hessianOperator (vectorEuclideanHistoryPotential s β t i) z
        (vectorEuclideanScoreShift s β t σ i z)) ≤
      inner ℝ (spinVector σ-vectorEuclideanMagnetization s β t i z)
        (vectorFieldHessian s β t (vectorEuclideanStateLinear s β t i z).1 (k+2-i)
          (vectorEuclideanStateLinear s β t i z).2
          (spinVector σ-vectorEuclideanMagnetization s β t i z)) := by
  by_cases hi : 0 < s.q i
  · exact (vectorEuclideanScoreShift_energy_eq s β t hβ ht σ i hi z).le
  · have hi0 : s.q i=0 := le_antisymm (le_of_not_gt hi) (s.q_nonneg (by omega))
    rw [vectorEuclideanScoreShift_zero_overlap s β t σ i hi0]
    simp only [map_zero,inner_zero_left]
    exact vectorFieldHessian_quadratic_nonneg _ _ _ _ _ _ _

end QuantitativePaper
