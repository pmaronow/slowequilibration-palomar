-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.DirectingPhysicalExclusion
public import SlowEquilibration.GaussianGGEnsemble
public import Mathlib.Topology.Compactness.Lindelof

/-! Replica exclusion for a random directing kernel. A countable open
subcover is selected before removing any disorder null sets, so the
uncountable family of excluded overlaps is handled correctly. The
hypotheses concern actual annealed finite IID replica events. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.DirectingPhysical

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open GaussianReplicaKernel GaussianGGEnsemble

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- A zero annealed IID event has zero conditional IID mass almost
surely. The real integral identity is proved for the genuine kernel. -/
theorem conditional_pi_zero_of_annealed_zero (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] (k : ℕ) (E : Set (Fin k → H))
    (hE : MeasurableSet E) (hzero : law d G k E = 0) :
    ∀ᵐ ω ∂d, Measure.pi (fun _ : Fin k => G ω) E = 0 := by
  have hm : Measurable (fun ω => (Measure.pi (fun _ : Fin k => G ω)).real E) := by
    simpa only [iid_apply, Measure.real] using
      ((iid G k).measurable_coe hE).ennreal_toReal
  have hi : Integrable (fun ω => (Measure.pi (fun _ : Fin k => G ω)).real E) d := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hzreal : (law d G k).real E = 0 := by simp [Measure.real, hzero]
  rw [replicaLaw_real_eq_integral d G k E hE] at hzreal
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => measureReal_nonneg) hi).mp hzreal
  filter_upwards [hae] with ω hω
  exact (ENNReal.toReal_eq_zero_iff _).mp hω |>.resolve_right (measure_ne_top _ _)

/-- Manuscript Lemma 6.5 for a measurable random directing measure.
Replica exclusion is assumed only for annealed open events, before
conditioning on the disorder. The entire support conclusion is proved. -/
theorem directing_norms_ae_mem_of_annealed_replica_exclusion
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (A : Set ℝ) (h0 : 0 ∈ A)
    (hball : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ≤ 1)
    (hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ∉ A →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ law d G k (equilateralEvent (H := H) k q ρ) = 0)
    (hcap : ∃ a < (1 : ℝ), law d G 2 (pairCapEvent (H := H) a) = 0) :
    ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ^ 2 ∈ A := by
  classical
  let B : Set ℝ := {q | q ∈ Ioo (0 : ℝ) 1 ∧ q ∉ A}
  choose k ρ hρ hzero using fun q : B => hexclude q.1 q.2.1 q.2.2
  let U : B → Set ℝ := fun q => {r | |r - q.1| < ρ q}
  have hUopen : ∀ q, IsOpen (U q) := fun q =>
    isOpen_lt (continuous_id.sub continuous_const).abs continuous_const
  have hcover : B ⊆ ⋃ q : B, U q := by
    intro q hq
    apply mem_iUnion.mpr
    refine ⟨⟨q, hq⟩, ?_⟩
    change |q - q| < ρ ⟨q, hq⟩
    simpa using hρ ⟨q, hq⟩
  obtain ⟨C, hCcount, hCcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof B).elim_countable_subcover U hUopen hcover
  let _ : Countable C := hCcount.to_subtype
  have haeC : ∀ᵐ ω ∂d, ∀ q : C,
      Measure.pi (fun _ : Fin (k q.1) => G ω)
        (equilateralEvent (H := H) (k q.1) q.1.1 (ρ q.1)) = 0 := by
    apply ae_all_iff.mpr
    intro q
    exact conditional_pi_zero_of_annealed_zero d G (k q.1) _
      (equilateralEvent_open _ _ _).measurableSet (hzero q.1)
  obtain ⟨a, ha, hcapzero⟩ := hcap
  have haeCap := conditional_pi_zero_of_annealed_zero d G 2 _
    (pairCapEvent_open a).measurableSet hcapzero
  filter_upwards [hball, haeC, haeCap] with ω hω hωC hωCap
  have hsball : (G ω).support ⊆ {v : H | ‖v‖ ≤ 1} :=
    Measure.support_subset_of_isClosed (isClosed_le continuous_norm continuous_const) hω
  filter_upwards [(G ω).support_mem_ae] with v hv
  by_contra hA
  have hq0 : 0 < ‖v‖ ^ 2 := by
    have hqne : ‖v‖ ^ 2 ≠ 0 := by
      intro hz
      exact hA (hz ▸ h0)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hqne)
  have hq1 : ‖v‖ ^ 2 < 1 :=
    (norm_sq_le_of_cap_zero (G ω) hωCap hv).trans_lt ha
  have hvB : ‖v‖ ^ 2 ∈ B := ⟨⟨hq0, hq1⟩, hA⟩
  obtain ⟨q, hqC, hnear⟩ := mem_iUnion₂.mp (hCcover hvB)
  exact norm_not_near_of_equilateral_zero (G ω) (hωC ⟨q, hqC⟩) hv hnear

end SlowEquilibration.DirectingPhysical
