module
public import QuantitativePaper.VectorConditionalMean
public import QuantitativePaper.VectorGradient
public import QuantitativePaper.VectorEuclideanCoordinates
public import QuantitativePaper.VectorHistoryLinear
public import FourPapersCommon.HistoryBackward

@[expose] public section

/-! Actual terminal-spin conditional means under the genuine normalized finite
vector path law, obtained by integrating its constructed Markov kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def vectorBackwardMean {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (d : Configuration n → ℝ) (i : ℕ) (x : VectorState n) : ℝ :=
  vectorConditionalMean s β t x.1 (fun _ => 0) d (k+2-i) 0 x.2

theorem measurable_vectorConditionalMean_state_zero {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun x : VectorState n => vectorConditionalMean s β t x.1 (fun _ => 0) d j 0 x.2) := by
  induction j with
  | zero =>
    unfold vectorConditionalMean terminalMean terminalWeight terminalPartition terminalTilt vectorTerminalExponent
      fieldDot energy Paper.skHamiltonian
    fun_prop
  | succ j ih =>
    simp only [vectorConditionalMean,vectorPerturbedRecursion_zero]
    exact measurable_vectorStepResponse_parameter
      (fun p x => vectorRecursion s β t p j x)
      (fun p x => vectorConditionalMean s β t p (fun _ => 0) d j 0 x)
      (measurable_vectorRecursion s β t j) ih _ _

theorem measurable_vectorBackwardMean {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) (i : ℕ) :
    Measurable (vectorBackwardMean s β t d i) :=
  measurable_vectorConditionalMean_state_zero s β t d (k+2-i)

theorem abs_vectorBackwardMean_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) (R : ℝ) (hd : ∀σ,|d σ|≤R)
    (i : ℕ) (x : VectorState n) : |vectorBackwardMean s β t d i x| ≤ R :=
  abs_vectorConditionalMean_le s β t x.1 (fun _ => 0) d R hd _ 0 x.2

theorem integral_vectorStateKernel_response {n : ℕ} (f : (Couplings n × ℝ) → Field n → ℝ)
    (hf : Measurable (fun x : VectorState n => f x.1 x.2))
    (K : ℝ≥0) (hfl : ∀p,LipschitzWith K (f p))
    (v : VectorState n → ℝ) (hv : Measurable v) (c m : ℝ) (x : VectorState n) :
    (∫y,v y ∂vectorStateKernel c m f x)=
      vectorStepResponse c m (f x.1) (fun z => v (x.1,z)) x.2 := by
  have hw : Measurable (vectorStateWeight c m f x) :=
    (measurable_vectorStateWeight f hf c m).comp (measurable_const.prodMk measurable_id)
  have hp (y : VectorState n) : 0 ≤ vectorStateWeight c m f x y :=
    div_nonneg (Real.exp_pos _).le (vectorStepPartition_pos (f x.1) K (hfl x.1) c m x.2).le
  rw [vectorStateKernel_apply f hf c m x,
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp _),smul_eq_mul]
  rw [vectorGaussianStateKernel_apply,
    integral_map (f := fun y => vectorStateWeight c m f x y*v y)
      (by unfold fieldShift;fun_prop) (hw.mul hv).aestronglyMeasurable]
  rfl

theorem vectorBackwardMean_kernel {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) (i : ℕ) (x : VectorState n) :
    vectorBackwardMean s β t d i x=
      ∫y,vectorBackwardMean s β t d (i+1) y ∂vectorProfileKernel s β t i x := by
  by_cases hi : i≤k+1
  · have hj : k+2-i=(k+1-i)+1 := by omega
    have hj' : k+2-(i+1)=k+1-i := by omega
    unfold vectorProfileKernel
    rw [ite_eq_left hi,integral_vectorStateKernel_response
      (fun p x => vectorRecursion s β t p (k+1-i) x) (measurable_vectorRecursion s β t _)
      (Real.sqrt (n : ℝ)).toNNReal (fun p => vectorRecursion_lipschitz s β t p _)
      _ (measurable_vectorBackwardMean s β t d (i+1))]
    unfold vectorBackwardMean
    rw [hj]
    have hqa : k+2-(k+1-i)=i+1 := by omega
    have hqb : k+1-(k+1-i)=i := by omega
    simp only [vectorConditionalMean,vectorPerturbedRecursion_zero,hj',hqa,hqb]
  · have hj : k+2-i=0 := by omega
    have hj' : k+2-(i+1)=0 := by omega
    simp [vectorProfileKernel,hi,Kernel.id_apply,vectorBackwardMean,hj,hj']

@[simp] theorem vectorBackwardMean_terminal {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) (x : VectorState n) :
    vectorBackwardMean s β t d (k+2) x=
      terminalMean (vectorTerminalExponent n β t x.1 x.2) d := by
  simp [vectorBackwardMean,vectorConditionalMean]

theorem vectorJointLaw_fst {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    (vectorJointLaw (n := n) s β t a).fst=vectorFieldHistoryLaw s β t a := by
  letI := vectorFieldHistoryLaw_probability (n := n) s β t a
  unfold vectorJointLaw
  exact Measure.fst_compProd _ _

theorem integral_vectorJointLaw_history {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (F : FiniteHistory (VectorState n) (k+2) → ℝ) (hF : Measurable F) :
    (∫p,F p.1 ∂vectorJointLaw s β t a)=∫h,F h ∂vectorFieldHistoryLaw s β t a := by
  have hm : (vectorJointLaw (n := n) s β t a).map Prod.fst=vectorFieldHistoryLaw s β t a :=
    vectorJointLaw_fst s β t a
  rw [←hm,integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable]

private theorem integrable_vector_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Measurable f) (K : ℝ) (hb : ∀x,|f x|≤K) : Integrable f P := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound hf.aestronglyMeasurable K
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem integral_vectorJointLaw_terminal_pairing_bound {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) (R : ℝ) (hd : ∀σ,|d σ|≤R)
    (i : ℕ) (hi : i≤k+2) (g : VectorState n → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p,g (historyObservation (k+2) i p.1)*d p.2 ∂vectorJointLaw s β t a)=
      ∫p,g (historyObservation (k+2) i p.1)*
        vectorBackwardMean s β t d i (historyObservation (k+2) i p.1) ∂vectorJointLaw s β t a := by
  letI := vectorJointLaw_probability (n := n) s β t a
  letI := vectorFieldHistoryLaw_probability (n := n) s β t a
  letI := vectorOuterLaw_probability (n := n) s β t a
  letI : IsProbabilityMeasure (vectorInitialLaw (n := n) s β t a) := by
    unfold vectorInitialLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hm : Measurable (fun p : FiniteHistory (VectorState n) (k+2) × Configuration n =>
      g (historyObservation (k+2) i p.1)*d p.2) :=
    (hg.comp ((measurable_historyObservation _ _).comp measurable_fst)).mul
      (measurable_of_finite d |>.comp measurable_snd)
  have hip := integrable_vector_bounded (vectorJointLaw s β t a) _ hm (K*R) (fun p => by
    rw [abs_mul]
    exact mul_le_mul (hK (historyObservation (k+2) i p.1)) (hd p.2) (abs_nonneg (d p.2))
      ((abs_nonneg (g (historyObservation (k+2) i p.1))).trans (hK (historyObservation (k+2) i p.1))))
  have he : (∫p,g (historyObservation (k+2) i p.1)*d p.2 ∂vectorJointLaw s β t a)=
      ∫h,g (historyObservation (k+2) i h)*vectorBackwardMean s β t d (k+2) (h (Fin.last (k+2)))
        ∂vectorFieldHistoryLaw s β t a := by
    rw [vectorJointLaw,Measure.integral_compProd hip]
    apply integral_congr_ae
    exact .of_forall fun h => by
      dsimp only
      change (∫σ,g (historyObservation (k+2) i h)*d σ
        ∂terminalLaw (vectorTerminalExponent n β t (h (Fin.last (k+2))).1 (h (Fin.last (k+2))).2))=_
      rw [integral_const_mul,integral_terminalLaw,vectorBackwardMean_terminal]
  rw [he,integral_vectorJointLaw_history s β t a
    (fun h => g (historyObservation (k+2) i h)*vectorBackwardMean s β t d i (historyObservation (k+2) i h))
    ((hg.comp (measurable_historyObservation _ _)).mul
      ((measurable_vectorBackwardMean s β t d i).comp (measurable_historyObservation _ _)))]
  exact integral_history_backward_pairing (vectorInitialLaw s β t a) (vectorProfileKernel s β t)
    (vectorProfileKernel_markov s β t) (vectorBackwardMean s β t d)
    (measurable_vectorBackwardMean s β t d) R (abs_vectorBackwardMean_le s β t d R hd)
    (vectorBackwardMean_kernel s β t d) (k+2) i hi g hg K hK

/-- Every finite terminal observable is bounded, so the actual pairing needs
no additional terminal-moment or conditional-law assumption. -/
theorem integral_vectorJointLaw_terminal_pairing {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ)
    (i : ℕ) (hi : i≤k+2) (g : VectorState n → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p,g (historyObservation (k+2) i p.1)*d p.2 ∂vectorJointLaw s β t a)=
      ∫p,g (historyObservation (k+2) i p.1)*
        vectorBackwardMean s β t d i (historyObservation (k+2) i p.1) ∂vectorJointLaw s β t a :=
  integral_vectorJointLaw_terminal_pairing_bound s β t a d (∑σ : Configuration n,|d σ|)
    (fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)) i hi g hg K hK

theorem integral_vectorEuclideanJointLaw_terminal_pairing {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ)
    (i : ℕ) (hi : i≤k+2) (g : VectorState n → ℝ) (hg : Measurable g)
    (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p : VectorGaussianSpace n k × Configuration n,
        g (vectorEuclideanStateLinear s β t i p.1)*d p.2 ∂vectorEuclideanJointLaw s β t a)=
      ∫p : VectorGaussianSpace n k × Configuration n,
        g (vectorEuclideanStateLinear s β t i p.1)*
        vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1)
          ∂vectorEuclideanJointLaw s β t a := by
  let F := fun p : FiniteHistory (VectorState n) (k+2) × Configuration n =>
    g (historyObservation (k+2) i p.1)*d p.2
  let G := fun p : FiniteHistory (VectorState n) (k+2) × Configuration n =>
    g (historyObservation (k+2) i p.1)*vectorBackwardMean s β t d i (historyObservation (k+2) i p.1)
  have hF : Measurable F :=
    (hg.comp ((measurable_historyObservation _ _).comp measurable_fst)).mul
      (measurable_of_finite d |>.comp measurable_snd)
  have hG : Measurable G :=
    (hg.comp ((measurable_historyObservation _ _).comp measurable_fst)).mul
      ((measurable_vectorBackwardMean s β t d i).comp
        ((measurable_historyObservation _ _).comp measurable_fst))
  have hh : (∫p,F p ∂vectorJointLaw s β t a)=∫p,G p ∂vectorJointLaw s β t a :=
    integral_vectorJointLaw_terminal_pairing s β t a d i hi g hg K hK
  rw [←vectorEuclideanJointLaw_map s β t a,
    integral_map (f := F) (measurable_vectorEuclideanJointMap s β t).aemeasurable hF.aestronglyMeasurable,
    integral_map (f := G) (measurable_vectorEuclideanJointMap s β t).aemeasurable hG.aestronglyMeasurable] at hh
  simpa only [F,G,vectorEuclideanJointMap,vectorCoordinateJointMap,historyObservation,
    vectorEuclideanStateLinear_apply] using hh

theorem vectorConditionalMean_zero_eq_response {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (d : Configuration n → ℝ) (j : ℕ) (x : Field n) :
    vectorConditionalMean s β t p (fun _ => 0) d j 0 x=
      vectorObservableResponse s β t p d j 0 x := by
  induction j generalizing x with
  | zero => simp [vectorConditionalMean,vectorObservableResponse,vectorTerminalObservable]
  | succ j ih =>
    simp only [vectorConditionalMean,vectorObservableResponse,vectorPerturbedRecursion_zero]
    congr 1
    funext z
    exact ih z

theorem vectorBackwardMean_spin {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (l : Fin n) :
    vectorBackwardMean s β t (fun σ => Paper.spinSign (σ l)) i x=
      vectorMagnetization s β t x.1 (k+2-i) x.2 l :=
  vectorConditionalMean_zero_eq_response s β t x.1 _ _ x.2

end QuantitativePaper
