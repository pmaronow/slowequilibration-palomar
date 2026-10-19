module
public import FourPapersCommon.HistoryBackward

@[expose] public section

/-! Backward expectation conditional on the entire retained Markov past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000
variable {State : Type*} [MeasurableSpace State]

def historyPrefix (n i : ℕ) (h : FiniteHistory State n) : FiniteHistory State i :=
  fun j => historyObservation n j h

theorem measurable_historyPrefix (n i : ℕ) :
    Measurable (historyPrefix (State := State) n i) :=
  Measurable.of_eval fun _ => measurable_historyObservation _ _

theorem historyPrefix_snoc (n i : ℕ) (hi : i≤n) (h : FiniteHistory State n) (y : State) :
    historyPrefix (n+1) i (Fin.snoc h y)=historyPrefix n i h := by
  funext j
  exact historyObservation_snoc n j (by omega) h y

@[simp] theorem historyPrefix_last (n i : ℕ) (h : FiniteHistory State n) :
    historyPrefix n i h (Fin.last i)=historyObservation n i h := rfl

private theorem integrable_bounded_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Measurable f) (K : ℝ) (hb : ∀x,|f x|≤K) : Integrable f P := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound hf.aestronglyMeasurable K
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem integral_history_prefix_step (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (n i : ℕ) (hi : i≤n) (g : FiniteHistory State i → ℝ) (f : State → ℝ)
    (hg : Measurable g) (hf : Measurable f)
    (K R : ℝ) (hK : ∀x,|g x|≤K) (hR : ∀x,|f x|≤R) :
    (∫h,g (historyPrefix (n+1) i h)*f (h (Fin.last (n+1))) ∂finiteHistoryLaw ν κ (n+1))=
      ∫h,g (historyPrefix n i h)*(∫y,f y ∂κ n (h (Fin.last n))) ∂finiteHistoryLaw ν κ n := by
  letI := isProbabilityMeasure_finiteHistoryLaw ν κ hκ n
  letI := hκ n
  let η := (κ n).comap (fun h : FiniteHistory State n => h (Fin.last n)) (measurable_pi_apply _)
  let P := (finiteHistoryLaw ν κ n) ⊗ₘ η
  have hm : Measurable (fun p : FiniteHistory State n × State => g (historyPrefix n i p.1)*f p.2) :=
    (hg.comp ((measurable_historyPrefix n i).comp measurable_fst)).mul (hf.comp measurable_snd)
  have hiP : Integrable (fun p : FiniteHistory State n × State =>
      g (historyPrefix n i p.1)*f p.2) P :=
    integrable_bounded_real P _ hm (K*R) (fun p => by
      rw [abs_mul]
      exact mul_le_mul (hK (historyPrefix n i p.1)) (hR p.2) (abs_nonneg (f p.2))
        ((abs_nonneg (g (historyPrefix n i p.1))).trans (hK (historyPrefix n i p.1))))
  rw [finiteHistoryLaw,(historySplit n).symm.measurableEmbedding.integral_map]
  simp only [historySplit_symm_apply,historyPrefix_snoc n i hi,Fin.snoc_last]
  rw [Measure.integral_compProd hiP]
  apply integral_congr_ae
  exact .of_forall fun h => by
    dsimp only
    rw [integral_const_mul]
    rfl

theorem integral_history_prefix_drop (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (n i : ℕ) (hi : i≤n) (g : FiniteHistory State i → ℝ)
    (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫h,g (historyPrefix (n+1) i h) ∂finiteHistoryLaw ν κ (n+1))=
      ∫h,g (historyPrefix n i h) ∂finiteHistoryLaw ν κ n := by
  letI := hκ n
  have hh := integral_history_prefix_step ν κ hκ n i hi g (fun _ => 1)
    hg measurable_const K 1 hK (fun _ => by norm_num)
  simpa using hh

theorem integral_history_backward_prefix_pairing (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (f : ℕ → State → ℝ) (hf : ∀j,Measurable (f j))
    (R : ℝ) (hR : ∀j x,|f j x|≤R)
    (hback : ∀j x,f j x=∫y,f (j+1) y ∂κ j x)
    (N i : ℕ) (hi : i≤N) (g : FiniteHistory State i → ℝ)
    (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫h,g (historyPrefix N i h)*f N (h (Fin.last N)) ∂finiteHistoryLaw ν κ N)=
      ∫h,g (historyPrefix N i h)*f i (historyObservation N i h) ∂finiteHistoryLaw ν κ N := by
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
      rw [integral_history_prefix_step ν κ hκ N i hi' g (f (N+1)) hg (hf _) K R hK (hR _)]
      simp_rw [←hback]
      rw [ih hi']
      symm
      have hh := integral_history_prefix_drop ν κ hκ N i hi'
        (fun p => g p*f i (p (Fin.last i)))
        (hg.mul ((hf i).comp (measurable_pi_apply _))) (K*R)
        (fun p => by
          rw [abs_mul]
          exact mul_le_mul (hK p) (hR i _) (abs_nonneg _) ((abs_nonneg (g p)).trans (hK p)))
      simpa only [historyPrefix_last] using hh

end FourPapersCommon
