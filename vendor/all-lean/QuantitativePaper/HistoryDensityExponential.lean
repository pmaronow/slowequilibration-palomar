module
public import QuantitativePaper.VectorNormalizedDensity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Exact exponential product and weighted summation-by-parts for chronological
histories. These are deterministic identities, with no probabilistic inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open FourPapersCommon

variable {State : Type*} [MeasurableSpace State]

def historyTransitionSum (e : ℕ → State → State → ℝ) (N : ℕ)
    (h : FiniteHistory State N) : ℝ :=
  ∑ i : Fin N,e i (h i.castSucc) (h i.succ)

theorem historyTransitionSum_snoc (e : ℕ → State → State → ℝ) (N : ℕ)
    (h : FiniteHistory State N) (y : State) :
    historyTransitionSum e (N+1) (Fin.snoc h y) =
      historyTransitionSum e N h+e N (h (Fin.last N)) y := by
  unfold historyTransitionSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_castSucc,Fin.snoc_castSucc]
    have he : i.castSucc.succ = i.succ.castSucc := by ext; rfl
    rw [he,Fin.snoc_castSucc]
  · simp only [Fin.val_last,Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc]

theorem finiteHistoryDensity_exp_sum (e : ℕ → State → State → ℝ) (N : ℕ)
    (h : FiniteHistory State N) :
    finiteHistoryDensity (fun i x y => ENNReal.ofReal (Real.exp (e i x y))) N h =
      ENNReal.ofReal (Real.exp (historyTransitionSum e N h)) := by
  induction N with
  | zero => simp [finiteHistoryDensity,historyTransitionSum]
  | succ N ih =>
    have he : h = Fin.snoc (fun i => h i.castSucc) (h (Fin.last (N+1))) :=
      (Fin.snoc_init_self h).symm
    rw [he,finiteHistoryDensity_snoc,ih,historyTransitionSum_snoc,Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem finiteHistoryDensity_eq_prod (w : ℕ → State → State → ℝ≥0∞) (N : ℕ)
    (h : FiniteHistory State N) :
    finiteHistoryDensity w N h = ∏ i : Fin N,w i (h i.castSucc) (h i.succ) := by
  induction N with
  | zero => simp [finiteHistoryDensity]
  | succ N ih =>
    have he : h = Fin.snoc (fun i => h i.castSucc) (h (Fin.last (N+1))) :=
      (Fin.snoc_init_self h).symm
    rw [he,finiteHistoryDensity_snoc,ih,Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_castSucc,Fin.snoc_castSucc]
      have hi : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      rw [hi,Fin.snoc_castSucc]
    · simp only [Fin.val_last,Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc]

theorem weighted_difference_sum (m u : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N+1),m i*(u (i+1)-u i)) =
      m N*u (N+1)-m 0*u 0-
        ∑ i ∈ Finset.range N,(m (i+1)-m i)*u (i+1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ring

end QuantitativePaper
