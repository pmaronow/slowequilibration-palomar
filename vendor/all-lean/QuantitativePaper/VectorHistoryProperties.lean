module
public import QuantitativePaper.VectorGaussianCoordinates

@[expose] public section

/-! The actual independent-coordinate history starts at zero field and retains
one disorder sample through every transition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

variable {State Noise A : Type*}

theorem independentHistory_initial (u : ℕ → State → Noise → State) (N : ℕ)
    (p : State × (Fin N → Noise)) : independentHistory u N p 0 = p.1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [independentHistory,Fin.snoc_apply_zero]
    exact ih _

theorem independentHistory_preserved (u : ℕ → State → Noise → State) (r : State → A)
    (hr : ∀ i x z,r (u i x z)=r x) (N : ℕ) (p : State × (Fin N → Noise))
    (i : Fin (N+1)) : r (independentHistory u N p i)=r p.1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [independentHistory,Fin.snoc_last]
      rw [hr]
      exact ih _ _
    · simp only [independentHistory,Fin.snoc_castSucc]
      exact ih _ _

theorem independentHistory_next (u : ℕ → State → Noise → State) (N : ℕ)
    (p : State × (Fin N → Noise)) (i : Fin N) :
    independentHistory u N p i.succ =
      u i (independentHistory u N p i.castSucc) (p.2 i) := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [independentHistory,Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc,Fin.val_last]
    · have he : j.castSucc.succ = j.succ.castSucc := by ext; rfl
      simp only [independentHistory,he,Fin.snoc_castSucc,Fin.val_castSucc]
      exact ih _ j

theorem vectorCoordinateUpdate_disorder {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (z : Field n) : (vectorCoordinateUpdate s β t i x z).1=x.1 := by
  unfold vectorCoordinateUpdate vectorStateUpdate
  split_ifs <;> rfl

theorem vectorCoordinateHistory_disorder {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorGaussianCoordinates n k) (i : Fin (k+3)) :
    (vectorCoordinateHistory s β t p i).1=p.1 :=
  independentHistory_preserved _ Prod.fst (vectorCoordinateUpdate_disorder s β t) _ _ i

theorem vectorCoordinateHistory_initial {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorGaussianCoordinates n k) : vectorCoordinateHistory s β t p 0=(p.1,0) :=
  independentHistory_initial _ _ _

theorem vectorCoordinateHistory_next {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : VectorGaussianCoordinates n k) (i : Fin (k+2)) :
    vectorCoordinateHistory s β t p i.succ =
      vectorCoordinateUpdate s β t i (vectorCoordinateHistory s β t p i.castSucc) (p.2 i) :=
  independentHistory_next _ _ _ i

end QuantitativePaper
