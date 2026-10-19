module
public import QuantitativePaper.VectorSpinPosterior
public import QuantitativePaper.VectorHistoryLinear
public import FourPapersCommon.GaussianSignFlips

@[expose] public section

/-! Actual spin gauge covariance of the finite Gaussian vector recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def spinGauge {n : ℕ} (η σ : Configuration n) : Configuration n :=
  fun i => if η i then σ i else !(σ i)

@[simp] theorem spinSign_spinGauge {n : ℕ} (η σ : Configuration n) (i : Fin n) :
    Paper.spinSign (spinGauge η σ i) = Paper.spinSign (η i)*Paper.spinSign (σ i) := by
  cases hη : η i <;> cases hσ : σ i <;> simp [spinGauge,Paper.spinSign,hη,hσ]

@[simp] theorem spinGauge_involutive {n : ℕ} (η σ : Configuration n) :
    spinGauge η (spinGauge η σ)=σ := by
  funext i
  cases hη : η i <;> cases hσ : σ i <;> simp [spinGauge,hη,hσ]

def spinGaugeEquiv {n : ℕ} (η : Configuration n) : Configuration n ≃ Configuration n where
  toFun := spinGauge η
  invFun := spinGauge η
  left_inv := spinGauge_involutive η
  right_inv := spinGauge_involutive η

theorem abs_spinSign {n : ℕ} (η : Configuration n) (i : Fin n) :
    |Paper.spinSign (η i)|=1 := by cases η i <;> norm_num [Paper.spinSign]

def fieldGauge {n : ℕ} (η : Configuration n) : Field n →L[ℝ] Field n :=
  coordinateSignCLM (fun i => Paper.spinSign (η i)) (abs_spinSign η)

@[simp] theorem fieldGauge_apply {n : ℕ} (η : Configuration n) (x : Field n) (i : Fin n) :
    fieldGauge η x i=Paper.spinSign (η i)*x i := rfl

def couplingGauge {n : ℕ} (η : Configuration n) (g : Couplings n) : Couplings n :=
  fun e => (Paper.spinSign (η e.val.1)*Paper.spinSign (η e.val.2))*g e

def completionGauge {n : ℕ} (η : Configuration n) (p : Couplings n × ℝ) : Couplings n × ℝ :=
  (couplingGauge η p.1,p.2)

theorem energy_gauge {n : ℕ} (η σ : Configuration n) (g : Couplings n) :
    energy n (couplingGauge η g) σ=energy n g (spinGauge η σ) := by
  unfold energy Paper.skHamiltonian
  simp only [zero_mul,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  simp only [couplingGauge,spinSign_spinGauge]
  ring

theorem fieldDot_gauge {n : ℕ} (η σ : Configuration n) (x : Field n) :
    fieldDot (fieldGauge η x) σ=fieldDot x (spinGauge η σ) := by
  unfold fieldDot
  apply Finset.sum_congr rfl
  intro i _
  simp only [fieldGauge_apply,spinSign_spinGauge]
  ring

theorem vectorTerminalExponent_gauge {n : ℕ} (η σ : Configuration n) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) :
    vectorTerminalExponent n β t (completionGauge η p) (fieldGauge η x) σ=
      vectorTerminalExponent n β t p x (spinGauge η σ) := by
  simp only [vectorTerminalExponent,completionGauge,energy_gauge,fieldDot_gauge]

theorem vectorTerminalPotential_gauge {n : ℕ} (η : Configuration n) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) :
    vectorTerminalPotential n β t (completionGauge η p) (fieldGauge η x)=
      vectorTerminalPotential n β t p x := by
  unfold vectorTerminalPotential terminalPotential terminalPartition
  simp_rw [vectorTerminalExponent_gauge]
  congr 1
  exact (spinGaugeEquiv η).sum_comp (fun σ => Real.exp (vectorTerminalExponent n β t p x σ))

theorem integral_fieldGauge {n : ℕ} (η : Configuration n) (f : Field n → ℝ) :
    (∫z,f (fieldGauge η z) ∂fieldGaussian n)=∫z,f z ∂fieldGaussian n := by
  apply (measurePreserving_coordinateSign _ (abs_spinSign η)).integral_comp
  exact (coordinateSignEquiv _ (abs_spinSign η)).toHomeomorph.measurableEmbedding

theorem fieldGauge_shift {n : ℕ} (η : Configuration n) (c : ℝ) (x z : Field n) :
    fieldShift c (fieldGauge η x) (fieldGauge η z)=fieldGauge η (fieldShift c x z) := by
  simp only [fieldShift,map_add,map_smul]

theorem vectorColeHopfStep_gauge {n : ℕ} (η : Configuration n) (c m : ℝ)
    (f g : Field n → ℝ) (hg : ∀x,g (fieldGauge η x)=f x) (x : Field n) :
    vectorColeHopfStep c m g (fieldGauge η x)=vectorColeHopfStep c m f x := by
  have hi : (∫z,g (fieldShift c (fieldGauge η x) z) ∂fieldGaussian n)=
      ∫z,f (fieldShift c x z) ∂fieldGaussian n := by
    rw [←integral_fieldGauge η (fun z => g (fieldShift c (fieldGauge η x) z))]
    simp_rw [fieldGauge_shift,hg]
  have he : vectorStepPartition c m g (fieldGauge η x)=vectorStepPartition c m f x := by
    unfold vectorStepPartition
    rw [←integral_fieldGauge η (fun z => Real.exp (m*g (fieldShift c (fieldGauge η x) z)))]
    simp_rw [fieldGauge_shift,hg]
  unfold vectorColeHopfStep
  split_ifs <;> simp only [hi,he]

theorem vectorRecursion_gauge {n k : ℕ} (s : RSBScheme k) (η : Configuration n)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorRecursion s β t (completionGauge η p) j (fieldGauge η x)=
      vectorRecursion s β t p j x := by
  induction j generalizing x with
  | zero => exact vectorTerminalPotential_gauge η β t p x
  | succ j ih => exact vectorColeHopfStep_gauge η _ _ _ _ ih x

def stateGauge {n : ℕ} (η : Configuration n) (x : VectorState n) : VectorState n :=
  (completionGauge η x.1,fieldGauge η x.2)

theorem independentHistory_covariant {State Noise : Type*}
    (u : ℕ → State → Noise → State) (G : State → State) (H : Noise → Noise)
    (hu : ∀i x z,u i (G x) (H z)=G (u i x z)) (N : ℕ)
    (p : State × (Fin N → Noise)) (i : Fin (N+1)) :
    independentHistory u N (G p.1,fun j => H (p.2 j)) i=
      G (independentHistory u N p i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [independentHistory,Fin.snoc_last]
      rw [ih (p.1,fun j => p.2 j.castSucc) (Fin.last N),hu]
    · simp only [independentHistory,Fin.snoc_castSucc]
      exact ih (p.1,fun j => p.2 j.castSucc) j

theorem vectorCoordinateUpdate_gauge {n k : ℕ} (s : RSBScheme k) (η : Configuration n)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (z : Field n) :
    vectorCoordinateUpdate s β t i (stateGauge η x) (fieldGauge η z)=
      stateGauge η (vectorCoordinateUpdate s β t i x z) := by
  unfold vectorCoordinateUpdate
  split_ifs
  · simp only [stateGauge,vectorStateUpdate,fieldGauge_shift]
  · rfl

def vectorGaugeSign {n k : ℕ} (η : Configuration n) : VectorGaussianIndex n k → ℝ
  | .inl none => 1
  | .inl (some e) => Paper.spinSign (η e.val.1)*Paper.spinSign (η e.val.2)
  | .inr (_,i) => Paper.spinSign (η i)

theorem abs_vectorGaugeSign {n k : ℕ} (η : Configuration n) (i : VectorGaussianIndex n k) :
    |vectorGaugeSign η i|=1 := by
  cases i with
  | inl i => cases i <;> simp only [vectorGaugeSign,abs_one,abs_mul,abs_spinSign,mul_one]
  | inr i => exact abs_spinSign η i.2

def vectorGaugeEquiv {n k : ℕ} (η : Configuration n) :
    VectorGaussianSpace n k ≃ₗᵢ[ℝ] VectorGaussianSpace n k :=
  coordinateSignEquiv (vectorGaugeSign η) (abs_vectorGaugeSign η)

def vectorGaussianGauge {n k : ℕ} (η : Configuration n) :
    VectorGaussianSpace n k →L[ℝ] VectorGaussianSpace n k :=
  coordinateSignCLM (vectorGaugeSign η) (abs_vectorGaugeSign η)

@[simp] theorem vectorGaussianGauge_apply {n k : ℕ} (η : Configuration n)
    (z : VectorGaussianSpace n k) (i : VectorGaussianIndex n k) :
    vectorGaussianGauge η z i=vectorGaugeSign η i*z i := rfl

theorem vectorEuclideanCoordinates_gauge {n k : ℕ} (η : Configuration n)
    (z : VectorGaussianSpace n k) :
    vectorEuclideanCoordinates n k (vectorGaussianGauge η z)=
      (completionGauge η (vectorEuclideanCoordinates n k z).1,
        fun j => fieldGauge η ((vectorEuclideanCoordinates n k z).2 j)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext e
      rfl
    · change Real.sqrt (1/2 : ℝ)*(1*z (.inl none))=Real.sqrt (1/2 : ℝ)*z (.inl none)
      ring
  · funext j
    ext i
    rfl

theorem vectorEuclideanHistory_gauge {n k : ℕ} (s : RSBScheme k) (η : Configuration n)
    (β t : ℝ) (z : VectorGaussianSpace n k) (i : Fin (k+3)) :
    vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k (vectorGaussianGauge η z)) i=
      stateGauge η (vectorCoordinateHistory s β t (vectorEuclideanCoordinates n k z) i) := by
  rw [vectorEuclideanCoordinates_gauge]
  unfold vectorCoordinateHistory
  have hi : stateGauge η ((vectorEuclideanCoordinates n k z).1,0)=
      (completionGauge η (vectorEuclideanCoordinates n k z).1,0) := by simp [stateGauge]
  rw [←hi]
  exact independentHistory_covariant _ _ _ (vectorCoordinateUpdate_gauge s η β t) (k+2)
    (((vectorEuclideanCoordinates n k z).1,0),(vectorEuclideanCoordinates n k z).2) i

theorem vectorEuclideanHistoryPotential_gauge {n k : ℕ} (s : RSBScheme k)
    (η : Configuration n) (β t : ℝ) (i : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanHistoryPotential s β t i (vectorGaussianGauge η z)=
      vectorEuclideanHistoryPotential s β t i z := by
  unfold vectorEuclideanHistoryPotential vectorHistoryPotential historyExtended
  rw [vectorEuclideanHistory_gauge]
  exact vectorRecursion_gauge _ _ _ _ _ _ _

theorem vectorEuclideanTerminalExponent_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t : ℝ) (z : VectorGaussianSpace n k) :
    vectorEuclideanTerminalExponent s β t σ (vectorGaussianGauge η z)=
      vectorEuclideanTerminalExponent s β t (spinGauge η σ) z := by
  unfold vectorEuclideanTerminalExponent
  rw [vectorEuclideanHistory_gauge]
  exact vectorTerminalExponent_gauge _ _ _ _ _ _

theorem vectorPosteriorPotential_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t a : ℝ) (z : VectorGaussianSpace n k) :
    vectorPosteriorPotential s β t a σ (vectorGaussianGauge η z)=
      vectorPosteriorPotential s β t a (spinGauge η σ) z := by
  have hn : ‖vectorGaussianGauge η z‖=‖z‖ := (vectorGaugeEquiv η).norm_map z
  simp only [vectorPosteriorPotential,standardGaussianPotential,hn,
    vectorEuclideanHistoryPotential_gauge,vectorEuclideanTerminalExponent_gauge]

theorem vectorGaussianGauge_volume_preserving {n k : ℕ} (η : Configuration n) :
    MeasurePreserving (vectorGaussianGauge (k := k) η)
      (volume : Measure (VectorGaussianSpace n k)) volume :=
  (vectorGaugeEquiv η).measurePreserving

theorem vectorSpinPosteriorMass_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t a : ℝ) :
    vectorSpinPosteriorMass s β t a (spinGauge η σ)=vectorSpinPosteriorMass s β t a σ := by
  unfold vectorSpinPosteriorMass QuantitativeFollowup.posteriorNormalizer
  rw [←(vectorGaussianGauge_volume_preserving (k := k) η).integral_comp
    (vectorGaugeEquiv η).toHomeomorph.measurableEmbedding
    (fun z => Real.exp (-vectorPosteriorPotential s β t a σ z))]
  simp_rw [vectorPosteriorPotential_gauge]

theorem vectorSpinPosteriorLaw_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t a : ℝ) :
    (vectorSpinPosteriorLaw s β t a (spinGauge η σ)).map (vectorGaussianGauge η)=
      vectorSpinPosteriorLaw s β t a σ := by
  have hp := vectorGaussianGauge_volume_preserving (k := k) η
  let W := fun z => ENNReal.ofReal (Real.exp
    (-QuantitativeFollowup.normalizedPosteriorPotential (vectorPosteriorPotential s β t a σ) z))
  have hw : Measurable W := (Real.continuous_exp.comp
    ((contDiff_vectorPosteriorPotential s β t a σ).continuous.add continuous_const).neg).measurable.ennreal_ofReal
  have he : (fun z => W (vectorGaussianGauge η z)) = fun z => ENNReal.ofReal (Real.exp
    (-QuantitativeFollowup.normalizedPosteriorPotential
      (vectorPosteriorPotential s β t a (spinGauge η σ)) z)) := by
    funext z
    unfold W QuantitativeFollowup.normalizedPosteriorPotential
    rw [vectorPosteriorPotential_gauge]
    change ENNReal.ofReal (Real.exp (-(vectorPosteriorPotential s β t a (spinGauge η σ) z+
      Real.log (vectorSpinPosteriorMass s β t a σ))))=_
    rw [←vectorSpinPosteriorMass_gauge s η σ β t a]
    rfl
  have hm := map_withDensity_pullback (volume : Measure (VectorGaussianSpace n k))
    (vectorGaussianGauge η) (vectorGaussianGauge η).measurable W hw
  rw [hp.map_eq,he] at hm
  exact hm

theorem vectorSpinPosterior_integral_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t a : ℝ) (f : VectorGaussianSpace n k → ℝ) :
    (∫z,f (vectorGaussianGauge η z) ∂vectorSpinPosteriorLaw s β t a (spinGauge η σ))=
      ∫z,f z ∂vectorSpinPosteriorLaw s β t a σ := by
  have he : MeasurableEmbedding (vectorGaussianGauge (k := k) η) :=
    (vectorGaugeEquiv η).toHomeomorph.measurableEmbedding
  rw [←he.integral_map f,vectorSpinPosteriorLaw_gauge]

@[simp] theorem spinGauge_connect {n : ℕ} (σ τ : Configuration n) :
    spinGauge (spinGauge σ τ) σ=τ := by
  funext i
  cases hσ : σ i <;> cases hτ : τ i <;> simp [spinGauge,hσ,hτ]

/-- Every gauge-covariant observable has the same actual normalized mean in
every spin slice. No equality of conditional means is supplied. -/
theorem vectorSpinPosterior_invariant_means {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (f : Configuration n → VectorGaussianSpace n k → ℝ)
    (hf : ∀η σ z,f σ (vectorGaussianGauge η z)=f (spinGauge η σ) z)
    (σ τ : Configuration n) :
    (∫z,f σ z ∂vectorSpinPosteriorLaw s β t a σ)=
      ∫z,f τ z ∂vectorSpinPosteriorLaw s β t a τ := by
  rw [←vectorSpinPosterior_integral_gauge s (spinGauge σ τ) σ β t a (f σ)]
  simp_rw [hf,spinGauge_connect]

end QuantitativePaper
