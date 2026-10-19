module
public import QuantitativePaper.VectorHistoryLinear

@[expose] public section

/-! Explicit retained field coordinates, including repeated overlap levels. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorFieldIncrement {k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : Fin (k+2)) : ℝ :=
  Real.sqrt ((1-t)*(β^2*(s.q (j+1)-s.q j)))

theorem vectorCoordinateHistory_field_sum {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : VectorGaussianCoordinates n k) (i : Fin (k+3)) :
    (vectorCoordinateHistory s β t p i).2=
      ∑ j : Fin (k+2),if j.val < i.val then vectorFieldIncrement s β t j • p.2 j else 0 := by
  classical
  refine Fin.induction ?_ (fun j ih => ?_) i
  · rw [vectorCoordinateHistory_initial]
    simp
  · rw [vectorCoordinateHistory_next]
    have hj : (j.val : ℕ) ≤ k+1 := by omega
    simp only [vectorCoordinateUpdate,if_pos hj,vectorStateUpdate,fieldShift,Prod.snd]
    rw [ih]
    have he (l : Fin (k+2)) :
        (if l.val < j.succ.val then vectorFieldIncrement s β t l • p.2 l else 0)=
        (if l.val < j.castSucc.val then vectorFieldIncrement s β t l • p.2 l else 0)+
          (if l=j then vectorFieldIncrement s β t j • p.2 j else 0) := by
      by_cases hlj : l=j
      · subst l
        simp
      · have hn : l.val≠j.val := fun h => hlj (Fin.ext h)
        by_cases hlt : l.val < j.val
        · simp [hlt,hlj,show l.val < j.val+1 by omega]
        · simp [hlt,hlj,show ¬l.val < j.val+1 by omega]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl

def vectorEuclideanFieldInsert (n k : ℕ) (j : Fin (k+2)) :
    Field n →L[ℝ] VectorGaussianSpace n k :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : VectorGaussianIndex n k => ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun a => match a with
      | Sum.inl _ => 0
      | Sum.inr (l,i) => if l=j then EuclideanSpace.proj i else 0)

theorem vectorEuclideanCoordinates_fieldInsert {n k : ℕ} (j : Fin (k+2)) (w : Field n) :
    vectorEuclideanCoordinates n k (vectorEuclideanFieldInsert n k j w)=
      ((0,0),fun l => if l=j then w else 0) := by
  apply Prod.ext
  · apply Prod.ext
    · funext e
      simp [vectorEuclideanCoordinates,vectorRawGaussianCoordinates,flatCompletionCoordinates,vectorEuclideanFieldInsert]
    · simp [vectorEuclideanCoordinates,vectorRawGaussianCoordinates,flatCompletionCoordinates,vectorEuclideanFieldInsert]
  · funext l
    apply PiLp.ext
    intro i
    by_cases hl : l=j <;> simp [vectorEuclideanCoordinates,vectorRawGaussianCoordinates,
      flatFieldCoordinates,vectorEuclideanFieldInsert,hl]

theorem vectorEuclideanStateLinear_fieldInsert {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : Fin (k+3)) (j : Fin (k+2)) (w : Field n) :
    vectorEuclideanStateLinear s β t i (vectorEuclideanFieldInsert n k j w)=
      (0,if j.val < i.val then vectorFieldIncrement s β t j • w else 0) := by
  classical
  rw [vectorEuclideanStateLinear_apply,vectorEuclideanCoordinates_fieldInsert]
  have hi : Fin.ofNat (k+3) i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hi]
  apply Prod.ext
  · exact vectorCoordinateHistory_disorder s β t _ i
  · rw [vectorCoordinateHistory_field_sum]
    simp only [Prod.snd]
    have he (l : Fin (k+2)) :
        (if l.val < i.val then vectorFieldIncrement s β t l • (if l=j then w else 0) else 0)=
        if l=j then (if j.val < i.val then vectorFieldIncrement s β t j • w else 0) else 0 := by
      by_cases hl : l=j
      · subst l
        simp
      · simp [hl]
    simp_rw [he]
    simp

end QuantitativePaper
