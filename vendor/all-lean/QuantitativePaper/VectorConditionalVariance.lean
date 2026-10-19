module
public import QuantitativePaper.VectorFiniteMartingale
public import QuantitativePaper.VectorHessianComparison
public import Mathlib.Probability.CondVar

@[expose] public section

/-! The genuine scalar conditional covariance of every finite terminal-spin
observable, identified with the analytically differentiated recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def vectorBackwardVariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (d : Configuration n → ℝ) (i : ℕ) (x : VectorState n) : ℝ :=
  vectorBackwardMean s β t (fun σ => d σ^2) i x-(vectorBackwardMean s β t d i x)^2

theorem condVar_vector_terminal_observable_past {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) (i : ℕ) (hi : i≤k+2) :
    condVar (vectorPastSigma s β t i) (fun p => d p.2) (vectorEuclideanJointLaw s β t a)
      =ᵐ[vectorEuclideanJointLaw s β t a]
      fun p => vectorBackwardVariance s β t d i (vectorEuclideanStateLinear s β t i p.1) := by
  let P := vectorEuclideanJointLaw (n := n) s β t a
  let R := ∑σ : Configuration n,|d σ|
  letI := vectorEuclideanJointLaw_probability (n := n) s β t a
  have hd (σ : Configuration n) : |d σ|≤R :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hLp : MemLp (fun p : VectorGaussianSpace n k × Configuration n => d p.2) 2 P :=
    MemLp.of_bound ((measurable_of_finite d).comp measurable_snd).aestronglyMeasurable R
      (.of_forall fun p => by simpa only [Real.norm_eq_abs] using hd p.2)
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (vectorPastSigma_le (n := n) s β t i) hLp
  have h1 := condExp_vector_terminal_observable_past s β t a d i hi
  have h2 := condExp_vector_terminal_observable_past s β t a (fun σ => d σ^2) i hi
  filter_upwards [hv,h1,h2] with p hp h1p h2p
  change condVar (vectorPastSigma s β t i) (fun p => d p.2) P p=
    P[(fun p => d p.2)^2 | vectorPastSigma s β t i] p-
      (P[(fun p => d p.2) | vectorPastSigma s β t i] p)^2 at hp
  rw [h1p,show (fun p : VectorGaussianSpace n k × Configuration n => d p.2)^2=
    (fun p => d p.2^2) from rfl,h2p] at hp
  exact hp

theorem vectorConditionalMean_zero_independent_tilt {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (j : ℕ) (x : Field n) :
    vectorConditionalMean s β t p b d j 0 x=
      vectorConditionalMean s β t p (fun _ => 0) d j 0 x := by
  induction j generalizing x with
  | zero => simp [vectorConditionalMean]
  | succ j ih =>
    simp only [vectorConditionalMean,vectorPerturbedRecursion_zero]
    congr 1
    funext z
    exact ih z

theorem vectorBackwardVariance_eq_observableCovariance {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) (i : ℕ) (x : VectorState n) :
    vectorBackwardVariance s β t d i x=
      vectorObservableCovariance s β t x.1 d (k+2-i) 0 x.2 := by
  unfold vectorBackwardVariance vectorBackwardMean vectorObservableCovariance
  rw [vectorConditionalMean_zero_independent_tilt s β t x.1 d (fun σ => d σ^2)]
  simp_rw [vectorConditionalMean_zero_eq_response]

theorem condVar_vector_terminal_eq_observableCovariance {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) (i : ℕ) (hi : i≤k+2) :
    condVar (vectorPastSigma s β t i) (fun p => d p.2) (vectorEuclideanJointLaw s β t a)
      =ᵐ[vectorEuclideanJointLaw s β t a]
      fun p => vectorObservableCovariance s β t (vectorEuclideanStateLinear s β t i p.1).1 d
        (k+2-i) 0 (vectorEuclideanStateLinear s β t i p.1).2 :=
  (condVar_vector_terminal_observable_past s β t a d i hi).trans
    (.of_forall fun _ => vectorBackwardVariance_eq_observableCovariance s β t d i _)

/-- The genuine second response is bounded above and below by the actual
conditional terminal variance, with the mass of its actual recursion cell. -/
theorem vectorSecondResponse_actual_conditionalVariance_bounds {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) (i : ℕ) (hi : i≤k+2) :
    ∀ᵐp ∂vectorEuclideanJointLaw s β t a,
      observableDepthMass s (k+2-i)*
          condVar (vectorPastSigma s β t i) (fun p => d p.2) (vectorEuclideanJointLaw s β t a) p ≤
        vectorObservableSecondResponse s β t (vectorEuclideanStateLinear s β t i p.1).1 d
          (k+2-i) 0 (vectorEuclideanStateLinear s β t i p.1).2 ∧
      vectorObservableSecondResponse s β t (vectorEuclideanStateLinear s β t i p.1).1 d
          (k+2-i) 0 (vectorEuclideanStateLinear s β t i p.1).2 ≤
        condVar (vectorPastSigma s β t i) (fun p => d p.2) (vectorEuclideanJointLaw s β t a) p := by
  let R : ℝ≥0 := ⟨∑σ : Configuration n,|d σ|,Finset.sum_nonneg fun _ _ => abs_nonneg _⟩
  have hb (σ : Configuration n) : |d σ|≤R :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)
  filter_upwards [condVar_vector_terminal_eq_observableCovariance s β t a d i hi] with p hp
  rw [hp]
  exact vectorObservableSecondResponse_covariance_bounds s β t _ d R hb _ 0 _

end QuantitativePaper
