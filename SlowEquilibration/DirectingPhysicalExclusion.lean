-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaKernel
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

/-! The support argument in manuscript Lemma 6.5. These are genuine finite
product measures, rather than an assumed constraint on directing norms.
The model-specific weak-limit and thermal replica-exclusion inputs remain
separate from this measure-theoretic implication. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.DirectingPhysical

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The literal open event of k replicas whose distinct pair overlaps
are all within rho of q. -/
def equilateralEvent (k : ℕ) (q ρ : ℝ) : Set (Fin k → H) :=
  {σ | ∀ i j : Fin k, i ≠ j → |inner ℝ (σ i) (σ j) - q| < ρ}

theorem equilateralEvent_open (k : ℕ) (q ρ : ℝ) :
    IsOpen (equilateralEvent (H := H) k q ρ) := by
  unfold equilateralEvent
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using isOpen_lt
      (((continuous_apply i).inner (continuous_apply j)).sub continuous_const).abs
      continuous_const

/-- A support point remains a support point when repeated in every
coordinate of the actual independent finite product. -/
theorem constantReplica_mem_support (ν : Measure H) [IsProbabilityMeasure ν]
    {v : H} (hv : v ∈ ν.support) (k : ℕ) :
    (fun _ : Fin k => v) ∈ (Measure.pi (fun _ : Fin k => ν)).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  apply lt_of_lt_of_le _ (measure_mono hball)
  rw [Measure.pi_ball _ _ hr]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact ne_of_gt ((Measure.mem_support_iff_forall v).mp hv _ (Metric.ball_mem_nhds _ hr))

/-- Zero probability of an open equilateral event rules out every
support point whose squared norm lies within its overlap window. -/
theorem norm_not_near_of_equilateral_zero (ν : Measure H)
    [IsProbabilityMeasure ν] {k : ℕ} {q ρ : ℝ}
    (hzero : Measure.pi (fun _ : Fin k => ν)
      (equilateralEvent (H := H) k q ρ) = 0)
    {v : H} (hv : v ∈ ν.support) :
    ¬ |‖v‖ ^ 2 - q| < ρ := by
  intro hnear
  have hmem : (fun _ : Fin k => v) ∈ equilateralEvent (H := H) k q ρ := by
    intro i j hij
    simpa only [real_inner_self_eq_norm_sq] using hnear
  have hpos := (Measure.mem_support_iff_forall (fun _ : Fin k => v)).mp
    (constantReplica_mem_support ν hv k) _ ((equilateralEvent_open k q ρ).mem_nhds hmem)
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- The actual two-replica cap event. -/
def pairCapEvent (a : ℝ) : Set (Fin 2 → H) :=
  {σ | a < inner ℝ (σ 0) (σ 1)}

theorem pairCapEvent_open (a : ℝ) : IsOpen (pairCapEvent (H := H) a) :=
  isOpen_lt continuous_const ((continuous_apply 0).inner (continuous_apply 1))

/-- A zero-mass cap event excludes support points whose squared norm
exceeds its threshold. This includes the source norm-one exclusion. -/
theorem norm_sq_le_of_cap_zero (ν : Measure H) [IsProbabilityMeasure ν]
    {a : ℝ} (hzero : Measure.pi (fun _ : Fin 2 => ν)
      (pairCapEvent (H := H) a) = 0) {v : H} (hv : v ∈ ν.support) :
    ‖v‖ ^ 2 ≤ a := by
  by_contra h
  have hmem : (fun _ : Fin 2 => v) ∈ pairCapEvent (H := H) a := by
    simpa only [pairCapEvent, mem_ofPred_eq, real_inner_self_eq_norm_sq]
      using (lt_of_not_ge h)
  have hpos := (Measure.mem_support_iff_forall (fun _ : Fin 2 => v)).mp
    (constantReplica_mem_support ν hv 2) _ ((pairCapEvent_open a).mem_nhds hmem)
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- Deterministic support-exclusion implication of manuscript Lemma 6.5.
The hypotheses are actual zero-probability replica events and the cap
estimate. No directing-norm support conclusion is assumed. -/
theorem norm_sq_mem_of_replica_exclusion (ν : Measure H)
    [IsProbabilityMeasure ν] (A : Set ℝ) (h0 : 0 ∈ A)
    (hball : ∀ᵐ v ∂ν, ‖v‖ ≤ 1)
    (hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ A →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        Measure.pi (fun _ : Fin k => ν) (equilateralEvent (H := H) k q ρ) = 0)
    (hcap : ∃ a < (1 : ℝ),
      Measure.pi (fun _ : Fin 2 => ν) (pairCapEvent (H := H) a) = 0) :
    ∀ᵐ v ∂ν, ‖v‖ ^ 2 ∈ A := by
  have hsball : ν.support ⊆ {v : H | ‖v‖ ≤ 1} :=
    Measure.support_subset_of_isClosed (isClosed_le continuous_norm continuous_const) hball
  obtain ⟨a, ha, hcapzero⟩ := hcap
  filter_upwards [ν.support_mem_ae] with v hv
  by_contra hA
  have hv1 := hsball hv
  have hq0 : 0 < ‖v‖ ^ 2 := by
    have hqne : ‖v‖ ^ 2 ≠ 0 := by
      intro hz
      exact hA (hz ▸ h0)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hqne)
  have hq1 : ‖v‖ ^ 2 < 1 :=
    (norm_sq_le_of_cap_zero ν hcapzero hv).trans_lt ha
  obtain ⟨k, ρ, hρ, hzero⟩ := hexclude (‖v‖ ^ 2) ⟨hq0, hq1⟩ hA
  exact norm_not_near_of_equilateral_zero ν hzero hv (by simpa using hρ)

end SlowEquilibration.DirectingPhysical
