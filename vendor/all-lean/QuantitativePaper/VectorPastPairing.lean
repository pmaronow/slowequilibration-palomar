module
public import QuantitativePaper.VectorConditionalExpectation
public import FourPapersCommon.HistoryBackwardPrefix

@[expose] public section

/-! Actual terminal-spin pairing against every bounded measurable retained
past record, including the initially tilted disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def vectorEuclideanPast {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (z : VectorGaussianSpace n k) : FiniteHistory (VectorState n) i :=
  historyPrefix (k+2) i (vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z))

theorem measurable_vectorEuclideanPast {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    Measurable (vectorEuclideanPast (n := n) s β t i) :=
  (measurable_historyPrefix _ _).comp ((measurable_vectorCoordinateHistory s β t).comp
    (measurable_vectorEuclideanCoordinates n k))

theorem vectorEuclideanPast_last {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanPast s β t i z (Fin.last i)=vectorEuclideanStateLinear s β t i z := by
  rw [vectorEuclideanStateLinear_apply]
  rfl

private theorem integrable_vector_past_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Measurable f) (K : ℝ) (hb : ∀x,|f x|≤K) : Integrable f P := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound hf.aestronglyMeasurable K
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem integral_vectorJointLaw_terminal_past_pairing_bound {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) (R : ℝ) (hd : ∀σ,|d σ|≤R)
    (i : ℕ) (hi : i≤k+2) (g : FiniteHistory (VectorState n) i → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p,g (historyPrefix (k+2) i p.1)*d p.2 ∂vectorJointLaw s β t a)=
      ∫p,g (historyPrefix (k+2) i p.1)*
        vectorBackwardMean s β t d i (historyObservation (k+2) i p.1) ∂vectorJointLaw s β t a := by
  letI := vectorJointLaw_probability (n := n) s β t a
  letI := vectorFieldHistoryLaw_probability (n := n) s β t a
  letI := vectorOuterLaw_probability (n := n) s β t a
  letI : IsProbabilityMeasure (vectorInitialLaw (n := n) s β t a) := by
    unfold vectorInitialLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hm : Measurable (fun p : FiniteHistory (VectorState n) (k+2) × Configuration n =>
      g (historyPrefix (k+2) i p.1)*d p.2) :=
    (hg.comp ((measurable_historyPrefix _ _).comp measurable_fst)).mul
      (measurable_of_finite d |>.comp measurable_snd)
  have hip := integrable_vector_past_bounded (vectorJointLaw s β t a) _ hm (K*R) (fun p => by
    rw [abs_mul]
    exact mul_le_mul (hK (historyPrefix (k+2) i p.1)) (hd p.2) (abs_nonneg (d p.2))
      ((abs_nonneg (g (historyPrefix (k+2) i p.1))).trans (hK (historyPrefix (k+2) i p.1))))
  have he : (∫p,g (historyPrefix (k+2) i p.1)*d p.2 ∂vectorJointLaw s β t a)=
      ∫h,g (historyPrefix (k+2) i h)*vectorBackwardMean s β t d (k+2) (h (Fin.last (k+2)))
        ∂vectorFieldHistoryLaw s β t a := by
    rw [vectorJointLaw,Measure.integral_compProd hip]
    apply integral_congr_ae
    exact .of_forall fun h => by
      dsimp only
      change (∫σ,g (historyPrefix (k+2) i h)*d σ
        ∂terminalLaw (vectorTerminalExponent n β t (h (Fin.last (k+2))).1 (h (Fin.last (k+2))).2))=_
      rw [integral_const_mul,integral_terminalLaw,vectorBackwardMean_terminal]
  rw [he,integral_vectorJointLaw_history s β t a
    (fun h => g (historyPrefix (k+2) i h)*vectorBackwardMean s β t d i (historyObservation (k+2) i h))
    ((hg.comp (measurable_historyPrefix _ _)).mul
      ((measurable_vectorBackwardMean s β t d i).comp (measurable_historyObservation _ _)))]
  exact integral_history_backward_prefix_pairing (vectorInitialLaw s β t a) (vectorProfileKernel s β t)
    (vectorProfileKernel_markov s β t) (vectorBackwardMean s β t d)
    (measurable_vectorBackwardMean s β t d) R (abs_vectorBackwardMean_le s β t d R hd)
    (vectorBackwardMean_kernel s β t d) (k+2) i hi g hg K hK

/-- Every finite terminal observable is bounded, so the actual pairing needs
no additional terminal-moment or conditional-law assumption. -/
theorem integral_vectorJointLaw_terminal_past_pairing {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ)
    (i : ℕ) (hi : i≤k+2) (g : FiniteHistory (VectorState n) i → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p,g (historyPrefix (k+2) i p.1)*d p.2 ∂vectorJointLaw s β t a)=
      ∫p,g (historyPrefix (k+2) i p.1)*
        vectorBackwardMean s β t d i (historyObservation (k+2) i p.1) ∂vectorJointLaw s β t a :=
  integral_vectorJointLaw_terminal_past_pairing_bound s β t a d (∑σ : Configuration n,|d σ|)
    (fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)) i hi g hg K hK

theorem integral_vectorEuclideanJointLaw_terminal_past_pairing {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ)
    (i : ℕ) (hi : i≤k+2) (g : FiniteHistory (VectorState n) i → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p : VectorGaussianSpace n k × Configuration n,
        g (vectorEuclideanPast s β t i p.1)*d p.2 ∂vectorEuclideanJointLaw s β t a)=
      ∫p : VectorGaussianSpace n k × Configuration n,
        g (vectorEuclideanPast s β t i p.1)*
        vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1)
          ∂vectorEuclideanJointLaw s β t a := by
  let F := fun p : FiniteHistory (VectorState n) (k+2) × Configuration n =>
    g (historyPrefix (k+2) i p.1)*d p.2
  let G := fun p : FiniteHistory (VectorState n) (k+2) × Configuration n =>
    g (historyPrefix (k+2) i p.1)*vectorBackwardMean s β t d i (historyObservation (k+2) i p.1)
  have hF : Measurable F :=
    (hg.comp ((measurable_historyPrefix _ _).comp measurable_fst)).mul
      (measurable_of_finite d |>.comp measurable_snd)
  have hG : Measurable G :=
    (hg.comp ((measurable_historyPrefix _ _).comp measurable_fst)).mul
      ((measurable_vectorBackwardMean s β t d i).comp
        ((measurable_historyObservation _ _).comp measurable_fst))
  have hh : (∫p,F p ∂vectorJointLaw s β t a)=∫p,G p ∂vectorJointLaw s β t a :=
    integral_vectorJointLaw_terminal_past_pairing s β t a d i hi g hg K hK
  rw [←vectorEuclideanJointLaw_map s β t a,
    integral_map (f := F) (measurable_vectorEuclideanJointMap s β t).aemeasurable hF.aestronglyMeasurable,
    integral_map (f := G) (measurable_vectorEuclideanJointMap s β t).aemeasurable hG.aestronglyMeasurable] at hh
  simpa only [F,G,vectorEuclideanPast,vectorEuclideanJointMap,vectorCoordinateJointMap,historyObservation,
    vectorEuclideanStateLinear_apply] using hh


end QuantitativePaper
