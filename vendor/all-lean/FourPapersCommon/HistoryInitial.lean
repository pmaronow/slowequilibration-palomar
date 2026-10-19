module
public import FourPapersCommon.HistoryBackward

@[expose] public section

/-! Retaining the initial law under every true finite Markov history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
variable {State : Type*} [MeasurableSpace State]

theorem integral_history_initial (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j)) (N : ℕ)
    (g : State → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x| ≤ K) :
    (∫h,g (historyObservation N 0 h) ∂finiteHistoryLaw ν κ N)=∫x,g x ∂ν := by
  induction N with
  | zero =>
    rw [finiteHistoryLaw]
    exact integral_map
      (show AEMeasurable (fun x : State => fun _ : Fin 1 => x) ν from (by fun_prop : Measurable (fun x : State => fun _ : Fin 1 => x)).aemeasurable)
      (f := fun h : FiniteHistory State 0 => g (historyObservation 0 0 h))
      (hg.comp (measurable_historyObservation 0 0)).aestronglyMeasurable
  | succ N ih =>
    rw [integral_history_observation_prefix ν κ hκ N 0 (Nat.zero_le _) g hg K hK,ih]

theorem integral_history_backward_at_initial (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀j,IsMarkovKernel (κ j))
    (f : ℕ → State → ℝ) (hf : ∀j,Measurable (f j))
    (R : ℝ) (hR : ∀j x,|f j x| ≤ R)
    (hback : ∀j x,f j x=∫y,f (j+1) y ∂κ j x) (N : ℕ) :
    (∫h,f N (h (Fin.last N)) ∂finiteHistoryLaw ν κ N)=∫x,f 0 x ∂ν := by
  have hh := integral_history_backward_pairing ν κ hκ f hf R hR hback N 0 (Nat.zero_le _)
    (fun _ => 1) measurable_const 1 (by simp)
  simp only [one_mul] at hh
  rw [hh]
  exact integral_history_initial ν κ hκ N (f 0) (hf 0) R (hR 0)

end FourPapersCommon
