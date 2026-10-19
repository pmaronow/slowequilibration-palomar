module
public import QuantitativePaper.VectorMagnetizationSmooth

@[expose] public section

/-! The manuscript's actual normalized spin/magnetization score and its free
Stieltjes weighted sum, on the full independent Gaussian coordinate model. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def vectorEuclideanOverlapScore {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) (i : ℕ) (z : VectorGaussianSpace n k) : ℝ :=
  (fieldDot (vectorEuclideanMagnetization s β t i z) σ-
    ‖vectorEuclideanMagnetization s β t i z‖^2/2)/(n : ℝ)

def vectorEuclideanWeightedOverlapScore {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (kernel : ℝ → ℝ) (σ : Configuration n) (z : VectorGaussianSpace n k) : ℝ :=
  (s.m 1-a)*kernel (s.q 1)*vectorEuclideanOverlapScore s β t σ 1 z+
    ∑ i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*kernel (s.q (i+2))*
      vectorEuclideanOverlapScore s β t σ (i+2) z

theorem boundedJets_vectorEuclideanOverlapScore {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (σ : Configuration n) (i : ℕ) :
    BoundedJets (vectorEuclideanOverlapScore (n := n) s β t σ i) := by
  let v := fun l : Fin n => fun z : VectorGaussianSpace n k => vectorEuclideanMagnetization s β t i z l
  have hv (l : Fin n) : BoundedJets (v l) := boundedJets_vectorEuclideanMagnetization_component s β t i l
  have hdot := boundedJets_finite_sum Finset.univ
    (fun l z => Paper.spinSign (σ l)*v l z) (fun l _ => (hv l).const_mul _)
  have hsq := boundedJets_finite_sum Finset.univ
    (fun l z => v l z*v l z) (fun l _ => (hv l).mul (hv l))
  have hh := (hdot.add (hsq.const_mul (-1/2))).const_mul ((n : ℝ)⁻¹)
  have he : vectorEuclideanOverlapScore (n := n) s β t σ i = fun z => (n : ℝ)⁻¹*
      ((∑ l : Fin n,Paper.spinSign (σ l)*v l z)+(-1/2)*(∑ l : Fin n,v l z*v l z)) := by
    funext z
    unfold vectorEuclideanOverlapScore fieldDot
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]
    simp_rw [mul_comm (vectorEuclideanMagnetization s β t i z _) (Paper.spinSign (σ _))]
    dsimp [v]
    ring
  rw [he]
  exact hh

theorem boundedJets_vectorEuclideanWeightedOverlapScore {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (kernel : ℝ → ℝ) (σ : Configuration n) :
    BoundedJets (vectorEuclideanWeightedOverlapScore (n := n) s β t a kernel σ) := by
  have h0 := (boundedJets_vectorEuclideanOverlapScore (n := n) s β t σ 1).const_mul
    ((s.m 1-a)*kernel (s.q 1))
  have hsum := boundedJets_finite_sum (Finset.range k)
    (fun i z => (s.m (i+2)-s.m (i+1))*kernel (s.q (i+2))*vectorEuclideanOverlapScore (n := n) s β t σ (i+2) z)
    (fun i _ => (boundedJets_vectorEuclideanOverlapScore s β t σ (i+2)).const_mul _)
  exact h0.add hsum

end QuantitativePaper
