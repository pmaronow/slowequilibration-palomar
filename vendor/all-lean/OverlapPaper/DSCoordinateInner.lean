module

public import OverlapPaper.DSHilbertCoordinates

@[expose] public section

/-! The actual Hilbert inner product is a Borel pointwise limit of continuous
finite-coordinate Gram functions. It is not asserted coordinate-continuous. -/
noncomputable section
open Set Filter MeasureTheory WithLp
open scoped Topology BigOperators RealInnerProductSpace lp
namespace OverlapPaper
set_option maxHeartbeats 800000

def coordinateInnerPrefix (M : ℕ) (v w : DSCoordinateBall) : ℝ :=
  ∑ i : Fin M,(v.1 i.val : ℝ)*(w.1 i.val : ℝ)

theorem continuous_coordinateInnerPrefix (M : ℕ) :
    Continuous (fun p : DSCoordinateBall×DSCoordinateBall => coordinateInnerPrefix M p.1 p.2) := by
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun v : DSCoordinateBall => (v.1 i.val : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply i.val).comp continuous_subtype_val)
  exact (hc.comp continuous_fst).mul (hc.comp continuous_snd)

theorem coordinateInnerPrefix_self_le_one (M : ℕ) (v : DSCoordinateBall) :
    coordinateInnerPrefix M v v ≤ 1 := by
  simp only [coordinateInnerPrefix,←sq]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (v.1 i : ℝ)^2) M]
  exact v.2 (Finset.range M)

theorem abs_coordinateInnerPrefix_le_one (M : ℕ) (v w : DSCoordinateBall) :
    |coordinateInnerPrefix M v w| ≤ 1 := by
  let a : EuclideanSpace ℝ (Fin M) := toLp 2 (fun i => (v.1 i.val : ℝ))
  let b : EuclideanSpace ℝ (Fin M) := toLp 2 (fun i => (w.1 i.val : ℝ))
  have ha : ‖a‖≤1 := by
    have hh : ‖a‖^2=coordinateInnerPrefix M v v := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [a,coordinateInnerPrefix,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    nlinarith [coordinateInnerPrefix_self_le_one M v,norm_nonneg a]
  have hb : ‖b‖≤1 := by
    have hh : ‖b‖^2=coordinateInnerPrefix M w w := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [b,coordinateInnerPrefix,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    nlinarith [coordinateInnerPrefix_self_le_one M w,norm_nonneg b]
  have hi : coordinateInnerPrefix M v w=⟪a,b⟫ := by
    simp only [a,b,coordinateInnerPrefix,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hi,←Real.norm_eq_abs]
  exact (norm_inner_le_norm a b).trans (by nlinarith [norm_nonneg a,norm_nonneg b])

theorem tendsto_coordinateInnerPrefix (v w : DSCoordinateBall) :
    Tendsto (fun M => coordinateInnerPrefix M v w) atTop
      (𝓝 ⟪coordinateVector v,coordinateVector w⟫) := by
  have hh := (lp.hasSum_inner (𝕜 := ℝ) (coordinateVector v) (coordinateVector w)).tendsto_sum_nat
  convert hh using 1
  ext M
  rw [coordinateInnerPrefix,Fin.sum_univ_eq_sum_range (fun i : ℕ => (v.1 i : ℝ)*(w.1 i : ℝ)) M]
  simp only [RCLike.inner_apply,conj_trivial,coordinateVector_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem measurable_coordinateInner :
    Measurable (fun p : DSCoordinateBall×DSCoordinateBall => ⟪coordinateVector p.1,coordinateVector p.2⟫) := by
  exact (measurable_coordinateVector.comp measurable_fst).inner
    (measurable_coordinateVector.comp measurable_snd)

theorem abs_coordinateInner_le_one (v w : DSCoordinateBall) :
    |⟪coordinateVector v,coordinateVector w⟫|≤1 := by
  rw [←Real.norm_eq_abs]
  apply (norm_inner_le_norm _ _).trans
  nlinarith [coordinateVector_norm_le_one v,coordinateVector_norm_le_one w,
    norm_nonneg (coordinateVector v),norm_nonneg (coordinateVector w)]

end OverlapPaper
