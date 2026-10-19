module
public import FourPapersCommon.FiniteHistory
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Genuine bounded backward expectation identities for finite Markov histories. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000

variable {State : Type*} [MeasurableSpace State]

def historyObservation (n i : ℕ) (h : FiniteHistory State n) : State :=
  h (Fin.ofNat (n+1) i)

theorem measurable_historyObservation (n i : ℕ) :
    Measurable (historyObservation (State := State) n i) := measurable_pi_apply _

theorem historyObservation_snoc (n i : ℕ) (hi : i≤n)
    (h : FiniteHistory State n) (y : State) :
    historyObservation (n+1) i (Fin.snoc h y)=historyObservation n i h := by
  have he : Fin.ofNat (n+2) i=(Fin.ofNat (n+1) i).castSucc := by
    ext
    change i % (n+2)=i % (n+1)
    simp only [Nat.mod_eq_of_lt (show i<n+2 by omega),Nat.mod_eq_of_lt (show i<n+1 by omega)]
  simp only [historyObservation,he,Fin.snoc_castSucc]

@[simp] theorem historyObservation_last (n : ℕ) (h : FiniteHistory State n) :
    historyObservation n n h=h (Fin.last n) := by
  have he : Fin.ofNat (n+1) n=Fin.last n := by
    ext
    simp
  simp only [historyObservation,he]

private theorem integrable_bounded_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Measurable f) (K : ℝ) (hb : ∀x,|f x|≤K) : Integrable f P := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound hf.aestronglyMeasurable K
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

/-- One true Markov step integrates a bounded backward value against the
retained earlier state. The actual earlier record is retained in the law. -/
theorem integral_history_observation_step (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (n i : ℕ) (hi : i≤n) (g f : State → ℝ)
    (hg : Measurable g) (hf : Measurable f)
    (K R : ℝ) (hK : ∀x,|g x|≤K) (hR : ∀x,|f x|≤R) :
    (∫h,g (historyObservation (n+1) i h)*f (h (Fin.last (n+1))) ∂finiteHistoryLaw ν κ (n+1))=
      ∫h,g (historyObservation n i h)*(∫y,f y ∂κ n (h (Fin.last n))) ∂finiteHistoryLaw ν κ n := by
  letI := isProbabilityMeasure_finiteHistoryLaw ν κ hκ n
  letI := hκ n
  let η := (κ n).comap (fun h : FiniteHistory State n => h (Fin.last n)) (measurable_pi_apply _)
  let P := (finiteHistoryLaw ν κ n) ⊗ₘ η
  have hm : Measurable (fun p : FiniteHistory State n × State => g (historyObservation n i p.1)*f p.2) :=
    (hg.comp ((measurable_historyObservation n i).comp measurable_fst)).mul (hf.comp measurable_snd)
  have hiP : Integrable (fun p : FiniteHistory State n × State =>
      g (historyObservation n i p.1)*f p.2) P :=
    integrable_bounded_real P _ hm (K*R) (fun p => by
      rw [abs_mul]
      exact mul_le_mul (hK (historyObservation n i p.1)) (hR p.2) (abs_nonneg (f p.2))
        ((abs_nonneg (g (historyObservation n i p.1))).trans (hK (historyObservation n i p.1))))
  rw [finiteHistoryLaw,(historySplit n).symm.measurableEmbedding.integral_map]
  simp only [historySplit_symm_apply,historyObservation_snoc n i hi,Fin.snoc_last]
  rw [Measure.integral_compProd hiP]
  apply integral_congr_ae
  exact .of_forall fun h => by
    dsimp only
    rw [integral_const_mul]
    rfl

theorem integral_history_observation_prefix (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (n i : ℕ) (hi : i≤n) (g : State → ℝ)
    (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫h,g (historyObservation (n+1) i h) ∂finiteHistoryLaw ν κ (n+1))=
      ∫h,g (historyObservation n i h) ∂finiteHistoryLaw ν κ n := by
  letI := hκ n
  have hh := integral_history_observation_step ν κ hκ n i hi g (fun _ => 1)
    hg measurable_const K 1 hK (fun _ => by norm_num)
  simpa using hh

/-- The genuinely integrated backward kernel recursion is the conditional
terminal expectation when paired with every bounded earlier-state test. -/
theorem integral_history_backward_pairing (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (f : ℕ → State → ℝ) (hf : ∀j,Measurable (f j))
    (R : ℝ) (hR : ∀j x,|f j x|≤R)
    (hback : ∀j x,f j x=∫y,f (j+1) y ∂κ j x)
    (N i : ℕ) (hi : i≤N) (g : State → ℝ)
    (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫h,g (historyObservation N i h)*f N (h (Fin.last N)) ∂finiteHistoryLaw ν κ N)=
      ∫h,g (historyObservation N i h)*f i (historyObservation N i h) ∂finiteHistoryLaw ν κ N := by
  induction N with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    simp
  | succ N ih =>
    by_cases hiN : i=N+1
    · subst i
      simp
    · have hi' : i≤N := by omega
      rw [integral_history_observation_step ν κ hκ N i hi' g (f (N+1)) hg (hf _) K R hK (hR _)]
      simp_rw [←hback]
      rw [ih hi']
      symm
      apply integral_history_observation_prefix ν κ hκ N i hi' (fun x => g x*f i x)
        (hg.mul (hf i)) (K*R)
      intro x
      rw [abs_mul]
      exact mul_le_mul (hK x) (hR i x) (abs_nonneg _) ((abs_nonneg (g x)).trans (hK x))

end FourPapersCommon
