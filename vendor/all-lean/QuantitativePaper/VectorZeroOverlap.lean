module
public import QuantitativePaper.VectorFieldRightInverse
public import QuantitativePaper.VectorMagnetizationGauge
public import QuantitativePaper.VectorOverlapScore

@[expose] public section

/-! Zero-overlap fields and scores vanish for the actual coordinate history,
even if the scheme contains several repeated zero levels. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorEuclideanState_zero_overlap {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i : Fin (k+3)) (hi : s.q i=0)
    (z : VectorGaussianSpace n k) : (vectorEuclideanStateLinear s β t i z).2=0 := by
  classical
  have hs := vectorFieldIncrement_prefix_sq s β t ht i
  rw [hi,mul_zero] at hs
  have hj (j : Fin (k+2)) (hj : j.val < i.val) : vectorFieldIncrement s β t j=0 := by
    have hb := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (k+2))))
      (f := fun l => if l.val < i.val then (vectorFieldIncrement s β t l)^2 else 0)
      (fun l _ => by split_ifs <;> positivity) (Finset.mem_univ j)
    rw [ite_eq_left hj,hs] at hb
    nlinarith [sq_nonneg (vectorFieldIncrement s β t j)]
  rw [vectorEuclideanStateLinear_apply]
  have he : Fin.ofNat (k+3) i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [he,vectorCoordinateHistory_field_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j.val < i.val
  · simp [hji,hj j hji]
  · simp [hji]

theorem vectorEuclideanMagnetization_zero_overlap {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i : Fin (k+3)) (hi : s.q i=0)
    (z : VectorGaussianSpace n k) : vectorEuclideanMagnetization s β t i z=0 := by
  unfold vectorEuclideanMagnetization
  rw [vectorEuclideanState_zero_overlap s β t ht i hi]
  exact vectorMagnetization_zero_field _ _ _ _ _

theorem vectorEuclideanOverlapScore_zero_overlap {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (σ : Configuration n) (i : Fin (k+3)) (hi : s.q i=0) :
    vectorEuclideanOverlapScore s β t σ i=fun _ => 0 := by
  funext z
  simp [vectorEuclideanOverlapScore,vectorEuclideanMagnetization_zero_overlap s β t ht i hi,
    fieldDot]

end QuantitativePaper
