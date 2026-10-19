module
public import QuantitativePaper.VectorHistoryLinear
public import QuantitativePaper.ConvexHessian

@[expose] public section

/-! Concrete posterior coercivity from the actual convex vector recursion.
The only floor hypotheses are the manuscript's mass inequality; the regularity
and Hessian lower bound are proved for the actual density potential. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem vectorEuclideanHistoryPotential_eq_comp {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) : vectorEuclideanHistoryPotential (n := n) s β t i =
      (fun p : VectorParameter n => vectorRecursion s β t p.1 (k+2-i) p.2) ∘
        vectorEuclideanStateLinear s β t i := by
  funext z
  rw [Function.comp_apply,vectorEuclideanStateLinear_apply]
  rfl

theorem convexOn_vectorEuclideanHistoryPotential {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) : ConvexOn ℝ univ (vectorEuclideanHistoryPotential (n := n) s β t i) := by
  rw [vectorEuclideanHistoryPotential_eq_comp]
  exact (convexOn_vectorRecursion_joint s β t (k+2-i)).comp_linearMap
    (vectorEuclideanStateLinear s β t i).toLinearMap

def vectorEuclideanTerminalLinear {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) : VectorGaussianSpace n k →L[ℝ] ℝ :=
  (vectorTerminalLinear n β t σ).comp (vectorEuclideanStateLinear s β t (k+2))

theorem vectorEuclideanTerminalLinear_apply {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (σ : Configuration n) (z : VectorGaussianSpace n k) :
    vectorEuclideanTerminalLinear s β t σ z=vectorEuclideanTerminalExponent s β t σ z := by
  rw [vectorEuclideanTerminalLinear,ContinuousLinearMap.comp_apply,
    vectorTerminalLinear_apply,vectorEuclideanStateLinear_apply]
  have he : Fin.ofNat (k+3) (k+2)=Fin.last (k+2) := by
    apply Fin.ext
    simp only [Fin.coe_ofNat_eq_mod,Fin.val_last]
    exact Nat.mod_eq_of_lt (by omega)
  rw [he]
  rfl

def vectorPosteriorCorrection {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (σ : Configuration n) : VectorGaussianSpace n k → ℝ :=
  fun z => vectorPosteriorPotential s β t a σ z-standardGaussianPotential z

theorem vectorPosteriorCorrection_eq {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (σ : Configuration n) : vectorPosteriorCorrection (n := n) s β t a σ = fun z =>
      -vectorEuclideanTerminalLinear s β t σ z+
      (s.m 1-a)*vectorEuclideanHistoryPotential s β t 1 z+
      (∑ i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*vectorEuclideanHistoryPotential s β t (i+2) z)+
      Real.log (vectorOuterPartition (n := n) s β t a) := by
  funext z
  rw [vectorEuclideanTerminalLinear_apply]
  unfold vectorPosteriorCorrection vectorPosteriorPotential
  ring

theorem convexOn_finite_sum_univ {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {ι : Type*} (S : Finset ι) (f : ι → A → ℝ) (hf : ∀ i ∈ S,ConvexOn ℝ univ (f i)) :
    ConvexOn ℝ univ (fun x => ∑ i ∈ S,f i x) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  calc
    _ ≤ ∑ i ∈ S,(a • f i x+b • f i y) :=
      Finset.sum_le_sum fun i hi => (hf i hi).2 hx hy ha hb hab
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum,smul_eq_mul]

theorem convexOn_vectorPosteriorCorrection {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (ha : a ≤ s.m 1) (σ : Configuration n) :
    ConvexOn ℝ univ (vectorPosteriorCorrection (n := n) s β t a σ) := by
  rw [vectorPosteriorCorrection_eq]
  have hc0 : ConvexOn ℝ univ (fun z => -vectorEuclideanTerminalLinear s β t σ z) :=
    (- (vectorEuclideanTerminalLinear s β t σ).toLinearMap).convexOn convex_univ
  have hc1 := (convexOn_vectorEuclideanHistoryPotential (n := n) s β t 1).smul
    (vectorFloorCoefficient_nonneg s a ha)
  have hcs := convexOn_finite_sum_univ (Finset.range k)
    (fun i z => (s.m (i+2)-s.m (i+1))*vectorEuclideanHistoryPotential (n := n) s β t (i+2) z)
    (fun i hi => by
      simpa only [smul_eq_mul] using (convexOn_vectorEuclideanHistoryPotential s β t (i+2)).smul
        (vectorStieltjesCoefficient_nonneg s (Finset.mem_range.mp hi)))
  convert! ((hc0.add hc1).add hcs).add_const (Real.log (vectorOuterPartition (n := n) s β t a)) using 1

theorem vectorPosteriorPotential_hessian_lower {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (ha : a ≤ s.m 1) (σ : Configuration n) (x z : VectorGaussianSpace n k) :
    ‖z‖^2 ≤ directionalHessian (vectorPosteriorPotential s β t a σ) x z := by
  have hs : ContDiff ℝ 2 (vectorPosteriorCorrection (n := n) s β t a σ) :=
    ((contDiff_vectorPosteriorPotential s β t a σ).sub contDiff_standardGaussianPotential).of_le (by simp)
  have he : vectorPosteriorPotential (n := n) s β t a σ =
      fun y => standardGaussianPotential y+vectorPosteriorCorrection s β t a σ y := by
    funext y
    unfold vectorPosteriorCorrection
    ring
  rw [he,directionalHessian_add _ _ (contDiff_standardGaussianPotential.of_le (by simp)) hs,
    directionalHessian_standardGaussianPotential]
  exact le_add_of_nonneg_right (directionalHessian_nonneg_of_convex _ hs
    (convexOn_vectorPosteriorCorrection s β t a ha σ) x z)

end QuantitativePaper
