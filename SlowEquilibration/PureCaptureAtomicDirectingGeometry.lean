-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCaptureAtomicDirectingGeometry

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [SecondCountableTopology H] [BorelSpace H] in
/-- Almost-sure pair-overlap support becomes a relation between every two
points of the directing support, by applying closedness twice. -/
theorem inner_on_support_of_pair_support
    (ν : Measure H) (Q : ℝ)
    (hpair : ∀ᵐ v ∂ν, ∀ᵐ w ∂ν, (inner ℝ v w) ∈ ({-Q, 0, Q} : Set ℝ)) :
    ∀ v ∈ ν.support, ∀ w ∈ ν.support,
      (inner ℝ v w) ∈ ({-Q, 0, Q} : Set ℝ) := by
  have hclosed : IsClosed ({-Q, 0, Q} : Set ℝ) := by
    exact (Set.toFinite _).isClosed
  have hfirst : ∀ᵐ v ∂ν, ∀ w ∈ ν.support,
      (inner ℝ v w) ∈ ({-Q, 0, Q} : Set ℝ) := by
    filter_upwards [hpair] with v hv
    exact ν.support_subset_of_isClosed (hclosed.preimage (by fun_prop)) hv
  intro v hv w hw
  exact ν.support_subset_of_isClosed (hclosed.preimage (by fun_prop))
    (hfirst.mono fun u hu => hu w hw) hv

omit [SecondCountableTopology H] [BorelSpace H] in
/-- Norm-Q vectors with the three-point pair law are either identical,
antipodal, or orthogonal. Distinct support vectors have a uniform gap. -/
theorem support_geometry
    (ν : Measure H) {Q : ℝ} (hQ : 0 < Q)
    (hnorm : ∀ᵐ v ∂ν, ‖v‖ ^ 2 = Q)
    (hpair : ∀ᵐ v ∂ν, ∀ᵐ w ∂ν, (inner ℝ v w) ∈ ({-Q, 0, Q} : Set ℝ)) :
    (∀ v ∈ ν.support, ‖v‖ ^ 2 = Q) ∧
      ∀ v ∈ ν.support, ∀ w ∈ ν.support, v ≠ w →
        (w = -v ∨ (inner ℝ v w) = 0) ∧ Real.sqrt (2 * Q) ≤ dist v w := by
  have hn : ∀ v ∈ ν.support, ‖v‖ ^ 2 = Q :=
    ν.support_subset_of_isClosed (isClosed_eq (by fun_prop) continuous_const) hnorm
  refine ⟨hn, ?_⟩
  intro v hv w hw hne
  have hi := inner_on_support_of_pair_support ν Q hpair v hv w hw
  simp only [mem_insert_iff, mem_singleton_iff] at hi
  have hineq : (inner ℝ v w) ≤ 0 := by
    rcases hi with hi | hi | hi
    · linarith
    · exact hi.le
    · have hz : ‖v - w‖ ^ 2 = 0 := by rw [norm_sub_sq_real, hn v hv, hn w hw, hi]; ring
      exact False.elim (hne (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))))
  constructor
  · rcases hi with hi | hi | hi
    · left
      have hz : ‖v + w‖ ^ 2 = 0 := by rw [norm_add_sq_real, hn v hv, hn w hw, hi]; ring
      have hsum := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
      exact eq_neg_of_add_eq_zero_right hsum
    · exact Or.inr hi
    · exact False.elim ((not_le_of_gt hQ) (hi ▸ hineq))
  · rw [dist_eq_norm]
    apply Real.sqrt_le_iff.mpr
    refine ⟨norm_nonneg _, ?_⟩
    rw [norm_sub_sq_real, hn v hv, hn w hw]
    linarith

/-- The true directing law is carried by a countable set of positive-mass
atoms. This proves atomicity from norm and pair laws, rather than assuming
atomic support. The same atoms satisfy the manuscript's geometry. -/
theorem countable_atomic_support
    (ν : Measure H) [IsProbabilityMeasure ν] {Q : ℝ} (hQ : 0 < Q)
    (hnorm : ∀ᵐ v ∂ν, ‖v‖ ^ 2 = Q)
    (hpair : ∀ᵐ v ∂ν, ∀ᵐ w ∂ν, (inner ℝ v w) ∈ ({-Q, 0, Q} : Set ℝ)) :
    ν.support.Countable ∧ ν ν.support = 1 ∧
      (∀ v ∈ ν.support, 0 < ν {v} ∧ ‖v‖ ^ 2 = Q) ∧
      ∀ v ∈ ν.support, ∀ w ∈ ν.support, v ≠ w →
        w = -v ∨ (inner ℝ v w) = 0 := by
  obtain ⟨hn, hgeom⟩ := support_geometry ν hQ hnorm hpair
  have hrad : 0 < Real.sqrt (2 * Q) / 2 := by positivity
  have hatom : ∀ v ∈ ν.support, 0 < ν {v} := by
    intro v hv
    have hball := (ν.mem_support_iff_forall v).mp hv
      (Metric.ball v (Real.sqrt (2 * Q) / 2)) (Metric.ball_mem_nhds v hrad)
    have heq : ν (Metric.ball v (Real.sqrt (2 * Q) / 2)) = ν {v} := by
      apply measure_congr
      filter_upwards [ν.support_mem_ae] with w hw
      apply propext
      constructor
      · intro hballw
        by_contra hne
        have hdist := (hgeom w hw v hv (by simpa only [mem_singleton_iff] using hne)).2
        have hlt := Metric.mem_ball.mp hballw
        linarith
      · intro heq
        rcases Set.mem_singleton_iff.mp heq with rfl
        exact Metric.mem_ball_self hrad
    rwa [heq] at hball
  have hcount : {v : H | 0 < ν {v}}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion
      (fun v => measurableSet_singleton v) (fun _ _ h => disjoint_singleton.mpr h)
  refine ⟨hcount.mono hatom, ?_, fun v hv => ⟨hatom v hv, hn v hv⟩,
    fun v hv w hw hne => (hgeom v hv w hw hne).1⟩
  rw [← measure_univ (μ := ν)]
  apply measure_congr
  filter_upwards [ν.support_mem_ae] with v hv
  simp [hv]

omit [InnerProductSpace ℝ H] in
/-- The countable support conclusion gives the literal sum-of-atoms
identity, with each atom weighted by its actual singleton mass. -/
theorem eq_sum_smul_dirac_support_of_countable
    (ν : Measure H) (hcount : ν.support.Countable) :
    ν = Measure.sum (fun v : ν.support => ν {(v : H)} • Measure.dirac (v : H)) := by
  let : Countable ν.support := hcount.to_subtype
  have hcover : (⋃ v : ν.support, ({(v : H)} : Set H)) = ν.support := by
    ext v
    simp only [mem_iUnion, mem_singleton_iff, Subtype.exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  calc
    ν = ν.restrict ν.support := (Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae).symm
    _ = ν.restrict (⋃ v : ν.support, ({(v : H)} : Set H)) := by rw [hcover]
    _ = Measure.sum (fun v : ν.support => ν.restrict {(v : H)}) :=
      Measure.restrict_iUnion (fun _ _ h => disjoint_singleton.mpr
        (fun heq => h (Subtype.ext heq))) (fun _ => measurableSet_singleton _)
    _ = _ := by simp_rw [Measure.restrict_singleton]

end SlowEquilibration.PureCaptureAtomicDirectingGeometry
