module
public import QuantitativePaper.VectorTailGaussianCoordinates

@[expose] public section

/-! Actual translation covariance of the entire remaining Gaussian history.
Every field coordinate is the initial field plus a fixed Gaussian increment
sum, while the single initial disorder is retained. -/
noncomputable section
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem independentHistory_state_conjugate {State Noise : Type*}
    (u : ℕ → State → Noise → State) (T : State → State)
    (hT : ∀i a z,u i (T a) z=T (u i a z)) (N : ℕ)
    (p : State × (Fin N → Noise)) (i : Fin (N+1)) :
    independentHistory u N (T p.1,p.2) i=T (independentHistory u N p i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [independentHistory,Fin.snoc_last]
      rw [ih (p.1,fun j => p.2 j.castSucc) (Fin.last N),hT]
    · simp only [independentHistory,Fin.snoc_castSucc]
      exact ih (p.1,fun l => p.2 l.castSucc) j

def vectorStateFieldTranslate (w : Field n) (z : VectorState n) : VectorState n := (z.1,z.2+w)

theorem vectorCoordinateUpdate_field_translate (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (w : Field n) (a : VectorState n) (z : Field n) :
    vectorCoordinateUpdate s β t i (vectorStateFieldTranslate w a) z=
      vectorStateFieldTranslate w (vectorCoordinateUpdate s β t i a z) := by
  unfold vectorCoordinateUpdate
  split_ifs
  · unfold vectorStateUpdate vectorStateFieldTranslate fieldShift
    apply Prod.ext
    · rfl
    · exact add_right_comm _ _ _
  · rfl

theorem vectorHistoryFrom_field_translate (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (x w : Field n) (j : ℕ) (z : Fin j → Field n)
    (i : Fin (j+1)) :
    vectorHistoryFrom s β t L p (x+w) j z i=
      vectorStateFieldTranslate w (vectorHistoryFrom s β t L p x j z i) :=
  independentHistory_state_conjugate (fun i => vectorCoordinateUpdate s β t (L+i))
    (vectorStateFieldTranslate w) (fun i => vectorCoordinateUpdate_field_translate s β t (L+i) w)
    j ((p,x),z) i

theorem vectorHistoryFrom_field_eq_initial_add (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (z : Fin j → Field n)
    (i : Fin (j+1)) :
    (vectorHistoryFrom s β t L p x j z i).2=x+(vectorHistoryFrom s β t L p 0 j z i).2 := by
  have hh := vectorHistoryFrom_field_translate s β t L p 0 x j z i
  simp only [zero_add,vectorStateFieldTranslate] at hh
  rw [hh]
  exact add_comm _ _

theorem contDiff_vectorHistoryFrom_initial_noise (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (fun z : Field n × (Fin j → Field n) => vectorHistoryFrom s β t L p z.1 j z.2) :=
  (contDiff_independentHistory ∞ _ (fun i => contDiff_vectorCoordinateUpdate s β t _ ∞) _).comp
    ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)

end QuantitativePaper
