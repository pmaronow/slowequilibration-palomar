module
public import FourPapersCommon.FiniteJointLaw
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Literal finite chronological path records and their Markov laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
namespace FourPapersCommon

abbrev FiniteHistory (State : Type*) (n : ℕ) := Fin (n + 1) → State

variable {State : Type*} [MeasurableSpace State]

def historySplit (n : ℕ) : FiniteHistory State (n + 1) ≃ᵐ FiniteHistory State n × State where
  toFun p := (fun i => p i.castSucc, p (Fin.last (n + 1)))
  invFun p := Fin.snoc p.1 p.2
  left_inv p := by funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := (Measurable.of_eval fun i => measurable_pi_apply i.castSucc).prodMk
    (measurable_pi_apply _)
  measurable_invFun := by
    change Measurable (fun p : FiniteHistory State n × State => (Fin.snoc p.1 p.2 : FiniteHistory State (n+1)))
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd : Measurable (fun p : FiniteHistory State n × State => p.2))
    · have hm : Measurable (fun p : FiniteHistory State n × State => p.1 j) :=
        (measurable_pi_apply j).comp measurable_fst
      simpa only [Fin.snoc_castSucc] using hm

@[simp] theorem historySplit_apply (n : ℕ) (p : FiniteHistory State (n + 1)) :
    historySplit n p = (fun i => p i.castSucc, p (Fin.last (n + 1))) := rfl

@[simp] theorem historySplit_symm_apply (n : ℕ) (p : FiniteHistory State n × State) :
    (historySplit n).symm p = Fin.snoc p.1 p.2 := rfl

def historySample {Ω : Type*} (X : ℝ≥0 → Ω → State) (T : ℕ → ℝ≥0) (n : ℕ)
    (sample : Ω) : FiniteHistory State n := fun i => X (T i) sample

theorem measurable_historySample {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → State) (hX : ∀ t, Measurable (X t)) (T : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (historySample X T n) := Measurable.of_eval fun i => hX _

def finiteHistoryLaw (ν : Measure State) (κ : ℕ → Kernel State State) :
    (n : ℕ) → Measure (FiniteHistory State n)
  | 0 => ν.map (fun x _ => x)
  | n + 1 => ((finiteHistoryLaw ν κ n) ⊗ₘ
      ((κ n).comap (fun p => p (Fin.last n)) (measurable_pi_apply _))).map
        (historySplit n).symm

theorem isProbabilityMeasure_finiteHistoryLaw (ν : Measure State) [IsProbabilityMeasure ν]
    (κ : ℕ → Kernel State State) (hκ : ∀ n, IsMarkovKernel (κ n)) (n : ℕ) :
    IsProbabilityMeasure (finiteHistoryLaw ν κ n) := by
  induction n with
  | zero =>
    change IsProbabilityMeasure (ν.map (fun x _ => x))
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  | succ n ih =>
    haveI := ih
    haveI := hκ n
    change IsProbabilityMeasure ((_ ⊗ₘ _).map (historySplit n).symm)
    exact (Measure.isProbabilityMeasure_map_iff (historySplit n).symm.measurable.aemeasurable).mpr inferInstance

/-- Every actual process with the given conditional kernels has the literal
finite Markov path law. The record of all previous values is retained. -/
theorem historySample_law_of_restricted {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → State) (hX : ∀ t, Measurable[F t] (X t))
    (T : ℕ → ℝ≥0) (hT : Monotone T)
    (κ : ℕ → Kernel State State) (hκ : ∀ n, IsMarkovKernel (κ n))
    (hlaw : ∀ n, ∀ E : Set Ω, MeasurableSet[F (T n)] E →
      (P.restrict E).map (X (T (n + 1))) = (κ n) ∘ₘ (P.restrict E).map (X (T n)))
    (n : ℕ) :
    P.map (historySample X T n) = finiteHistoryLaw (P.map (X (T 0))) κ n := by
  have hXg (t : ℝ≥0) : Measurable (X t) := (hX t).mono (F.le t) le_rfl
  induction n with
  | zero =>
    rw [finiteHistoryLaw, Measure.map_map (by fun_prop) (hXg _)]
    congr 1
    funext sample i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    simp only [historySample, Function.comp_def, hi, Fin.val_zero]
  | succ n ih =>
    haveI := hκ n
    have hY : Measurable[F (T n)] (historySample X T n) := by
      letI : MeasurableSpace Ω := F (T n)
      apply Measurable.of_eval
      intro i
      exact (hX (T i)).mono (F.mono (hT (show (i : ℕ) ≤ n from by omega))) le_rfl
    have hρ : Measurable (fun p : FiniteHistory State n => p (Fin.last n)) := measurable_pi_apply _
    have hj := joint_transitionLaw_of_restricted (F (T n)) P (F.le _)
      (historySample X T n) hY (X (T n)) (X (T (n + 1))) (hXg _) (hXg _)
      (fun p => p (Fin.last n)) hρ (fun _ => rfl) (κ n) (hlaw n)
    change P.map (historySample X T (n + 1)) =
      ((finiteHistoryLaw (P.map (X (T 0))) κ n) ⊗ₘ ((κ n).comap _ _)).map (historySplit n).symm
    rw [← ih, ← hj,
      Measure.map_map (historySplit n).symm.measurable
        ((measurable_historySample X hXg T n).prodMk (hXg _))]
    congr 1
    funext sample
    apply (historySplit n).injective
    simp only [MeasurableEquiv.apply_symm_apply, historySplit_apply, historySample,
      Fin.val_castSucc, Fin.val_last, Function.comp_def]
    rfl

end FourPapersCommon
