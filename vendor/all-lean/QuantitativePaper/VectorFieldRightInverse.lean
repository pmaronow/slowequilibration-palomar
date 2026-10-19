module
public import QuantitativePaper.VectorHistoryField

@[expose] public section

/-! A genuine right inverse of each positive-overlap field map. It uses all
revealed field increments and therefore permits repeated or zero-variance
cells without choosing a strictly positive first increment. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem fin_prefix_sum_succ {N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin N → A) (j : Fin N) :
    (∑ l : Fin N,if l.val < j.succ.val then f l else 0)=
      (∑ l : Fin N,if l.val < j.castSucc.val then f l else 0)+f j := by
  classical
  have he (l : Fin N) :
      (if l.val < j.succ.val then f l else 0)=
      (if l.val < j.castSucc.val then f l else 0)+(if l=j then f j else 0) := by
    by_cases hlj : l=j
    · subst l
      simp
    · have hn : l.val≠j.val := fun h => hlj (Fin.ext h)
      by_cases hlt : l.val < j.val
      · simp [hlt,hlj,show l.val < j.val+1 by omega]
      · simp [hlt,hlj,show ¬l.val < j.val+1 by omega]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem vectorFieldIncrement_sq {k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (ht : t ≤ 1) (j : Fin (k+2)) :
    (vectorFieldIncrement s β t j)^2=(1-t)*β^2*(s.q (j+1)-s.q j) := by
  unfold vectorFieldIncrement
  rw [Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht)
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (s.q_mono j (by omega)))))]
  ring

theorem vectorFieldIncrement_prefix_sq {k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (ht : t ≤ 1) (i : Fin (k+3)) :
    (∑ j : Fin (k+2),if j.val < i.val then (vectorFieldIncrement s β t j)^2 else 0)=
      (1-t)*β^2*s.q i := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp [s.q_zero]
  · rw [fin_prefix_sum_succ,ih,vectorFieldIncrement_sq s β t ht]
    simp only [Fin.val_succ,Fin.val_castSucc]
    ring

def vectorEuclideanFieldRightInverse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin (k+3)) : Field n →L[ℝ] VectorGaussianSpace n k :=
  ∑ j : Fin (k+2),
    (if j.val < i.val then vectorFieldIncrement s β t j/((1-t)*β^2*s.q i) else 0) •
      vectorEuclideanFieldInsert n k j

theorem vectorEuclideanStateLinear_rightInverse {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t < 1) (i : Fin (k+3)) (hi : 0 < s.q i)
    (w : Field n) :
    vectorEuclideanStateLinear s β t i (vectorEuclideanFieldRightInverse s β t i w)=(0,w) := by
  classical
  have hd : 0 < (1-t)*β^2*s.q i := mul_pos (mul_pos (by linarith) (sq_pos_of_ne_zero hβ)) hi
  rw [vectorEuclideanFieldRightInverse,sum_apply,map_sum]
  simp_rw [smul_apply,map_smul,vectorEuclideanStateLinear_fieldInsert]
  apply Prod.ext
  · simp only [Prod.fst_sum,Prod.smul_mk,Prod.fst,smul_zero,Finset.sum_const_zero]
  · simp only [Prod.snd_sum,Prod.smul_mk,Prod.snd]
    change (∑ j : Fin (k+2),
      (if j.val < i.val then vectorFieldIncrement s β t j/((1-t)*β^2*s.q i) else 0) •
        (if j.val < i.val then vectorFieldIncrement s β t j • w else 0))=w
    have he (j : Fin (k+2)) :
        (if j.val < i.val then vectorFieldIncrement s β t j/((1-t)*β^2*s.q i) else 0) •
          (if j.val < i.val then vectorFieldIncrement s β t j • w else 0)=
        ((if j.val < i.val then (vectorFieldIncrement s β t j)^2 else 0)/
          ((1-t)*β^2*s.q i)) • w := by
      by_cases hj : j.val < i.val
      · simp only [ite_eq_left hj,smul_smul]
        congr 1
        ring
      · simp [hj]
    simp_rw [he]
    rw [←Finset.sum_smul,←Finset.sum_div,vectorFieldIncrement_prefix_sq s β t ht.le,
      div_self hd.ne',one_smul]

end QuantitativePaper
