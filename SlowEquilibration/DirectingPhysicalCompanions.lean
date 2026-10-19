-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.DirectingPhysicalNorm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual finite independent directing replicas contain an arbitrary
fixed number of companions at overlap Q, with probability tending to
one as the number of independent blocks grows. This is the directing
measure step of manuscript Propositions 9.16 and 12.10. No atomicity,
ultrametricity, or presumed successful-replica probability is used. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.DirectingPhysical

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- A group of n companions, all with mutual overlaps and overlaps with
the distinguished vector within theta of Q. -/
def pointedEquilateralEvent (n : ℕ) (v : H) (Q θ : ℝ) : Set (Fin n → H) :=
  equilateralEvent n Q θ ∩ {σ | ∀ i : Fin n, |inner ℝ v (σ i) - Q| < θ}

def jointPointedEquilateralEvent (n : ℕ) (Q θ : ℝ) : Set (H × (Fin n → H)) :=
  {p | p.2 ∈ pointedEquilateralEvent n p.1 Q θ}

theorem jointPointedEquilateralEvent_open (n : ℕ) (Q θ : ℝ) :
    IsOpen (jointPointedEquilateralEvent (H := H) n Q θ) := by
  have hpair : IsOpen {p : H × (Fin n → H) |
      ∀ i : Fin n, |inner ℝ p.1 (p.2 i) - Q| < θ} := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt ((continuous_fst.inner ((continuous_apply i).comp continuous_snd)).sub
      continuous_const).abs continuous_const
  exact ((equilateralEvent_open n Q θ).preimage continuous_snd).inter hpair

theorem pointedEquilateralEvent_open (n : ℕ) (v : H) (Q θ : ℝ) :
    IsOpen (pointedEquilateralEvent n v Q θ) :=
  (jointPointedEquilateralEvent_open n Q θ).preimage (continuous_const.prodMk continuous_id)

/-- The true probability of one successful independent block. -/
def companionBlockMass (ν : Measure H) (n : ℕ) (Q θ : ℝ) (v : H) : ℝ :=
  (Measure.pi (fun _ : Fin n => ν)).real (pointedEquilateralEvent n v Q θ)

theorem companionBlockMass_measurable (ν : Measure H) [IsProbabilityMeasure ν]
    (n : ℕ) (Q θ : ℝ) : Measurable (companionBlockMass ν n Q θ) := by
  exact (Kernel.measurable_kernel_prodMk_left
    (κ := Kernel.const H (Measure.pi (fun _ : Fin n => ν)))
    (jointPointedEquilateralEvent_open n Q θ).measurableSet).ennreal_toReal

/-- Every support vector on the Q sphere has a positive chance of an
entire companion block. This follows from open-product support. -/
theorem companionBlockMass_pos (ν : Measure H) [IsProbabilityMeasure ν]
    (n : ℕ) {Q θ : ℝ} (hθ : 0 < θ) {v : H}
    (hv : v ∈ ν.support) (hvQ : ‖v‖ ^ 2 = Q) :
    0 < companionBlockMass ν n Q θ v := by
  have hmem : (fun _ : Fin n => v) ∈ pointedEquilateralEvent n v Q θ := by
    constructor
    · intro i j hij
      simpa only [real_inner_self_eq_norm_sq, hvQ, sub_self, abs_zero] using hθ
    · intro i
      simpa only [real_inner_self_eq_norm_sq, hvQ, sub_self, abs_zero] using hθ
  have hpos := (Measure.mem_support_iff_forall (fun _ : Fin n => v)).mp
    (constantReplica_mem_support ν hv n) _ ((pointedEquilateralEvent_open n v Q θ).mem_nhds hmem)
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)

/-- Failure to find a successful companion group among k independent
blocks of n replicas. All samples, including the query vector, have
their actual ordinary independent product law. -/
def companionFailureEvent (n : ℕ) (Q θ : ℝ) (k : ℕ) :
    Set (H × (Fin k → (Fin n → H))) :=
  {p | ∀ b : Fin k, p.2 b ∉ pointedEquilateralEvent n p.1 Q θ}

theorem companionFailureEvent_closed (n : ℕ) (Q θ : ℝ) (k : ℕ) :
    IsClosed (companionFailureEvent (H := H) n Q θ k) := by
  unfold companionFailureEvent
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro b
  have hmap : Continuous (fun p : H × (Fin k → (Fin n → H)) => (p.1, p.2 b)) :=
    continuous_fst.prodMk ((continuous_apply b).comp continuous_snd)
  exact (jointPointedEquilateralEvent_open (H := H) n Q θ).isClosed_compl.preimage hmap

/-- Exact geometric failure formula at a fixed query vector. -/
theorem companionFailure_row_mass (ν : Measure H) [IsProbabilityMeasure ν]
    (n : ℕ) (Q θ : ℝ) (k : ℕ) (v : H) :
    (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n => ν))).real
      {σ | (v, σ) ∈ companionFailureEvent n Q θ k} =
        (1 - companionBlockMass ν n Q θ v) ^ k := by
  have hset : {σ | (v, σ) ∈ companionFailureEvent (H := H) n Q θ k} =
      univ.pi (fun _ : Fin k => (pointedEquilateralEvent n v Q θ)ᶜ) := by
    ext σ
    simp [companionFailureEvent, Set.mem_pi]
  rw [hset, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Measure.real,
    probReal_compl_eq_one_sub (pointedEquilateralEvent_open n v Q θ).measurableSet]
  rfl

/-- Exact annealed finite-product expression: a probability of actual
replica failure equals the averaged independent-block geometric term. -/
theorem companionFailure_mass_eq_integral (ν : Measure H) [IsProbabilityMeasure ν]
    (n : ℕ) (Q θ : ℝ) (k : ℕ) :
    (ν.prod (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n => ν)))).real
      (companionFailureEvent n Q θ k) =
        ∫ v, (1 - companionBlockMass ν n Q θ v) ^ k ∂ν := by
  have hE := (companionFailureEvent_closed (H := H) n Q θ k).measurableSet
  rw [← integral_indicator_one hE,
    integral_prod _ ((integrable_const 1).indicator hE)]
  apply integral_congr_ae
  exact .of_forall fun v => by
    change (∫ σ, (companionFailureEvent n Q θ k).indicator (fun _ => (1 : ℝ)) (v, σ)
      ∂Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n => ν))) = _
    have hrow : MeasurableSet {σ | (v, σ) ∈ companionFailureEvent (H := H) n Q θ k} :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have hind : (fun σ => (companionFailureEvent n Q θ k).indicator (fun _ => (1 : ℝ)) (v, σ)) =
        ({σ | (v, σ) ∈ companionFailureEvent n Q θ k}).indicator (fun _ => (1 : ℝ)) := rfl
    rw [hind, integral_indicator_const 1 hrow, smul_eq_mul, mul_one, companionFailure_row_mass]

/-- As the number of actual additional IID blocks grows, the probability
of not finding n companions at overlap Q tends to zero. The successful
block probability is proved positive from support, not assumed. -/
theorem companionFailure_mass_tendsto_zero (ν : Measure H) [IsProbabilityMeasure ν]
    (n : ℕ) {Q θ : ℝ} (hθ : 0 < θ) (hν : ∀ᵐ v ∂ν, ‖v‖ ^ 2 = Q) :
    Tendsto (fun k =>
      (ν.prod (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n => ν)))).real
        (companionFailureEvent n Q θ k)) atTop (𝓝 0) := by
  simp_rw [companionFailure_mass_eq_integral]
  have hm := companionBlockMass_measurable ν n Q θ
  have hconv : ∀ᵐ v ∂ν, Tendsto (fun k => (1 - companionBlockMass ν n Q θ v) ^ k)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hν, ν.support_mem_ae] with v hvQ hv
    have hpos := companionBlockMass_pos ν n hθ hv hvQ
    have hle : companionBlockMass ν n Q θ v ≤ 1 := measureReal_le_one
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hle) (by linarith)
  have hbound : ∀ k : ℕ, ∀ᵐ v ∂ν, ‖(1 - companionBlockMass ν n Q θ v) ^ k‖ ≤ (1 : ℝ) := by
    intro k
    exact .of_forall fun v => by
      have h0 : 0 ≤ companionBlockMass ν n Q θ v := measureReal_nonneg
      have h1 : companionBlockMass ν n Q θ v ≤ 1 := measureReal_le_one
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr h1) k)]
      exact pow_le_one₀ (sub_nonneg.mpr h1) (by linarith)
  have hi := tendsto_integral_of_dominated_convergence (fun _ : H => (1 : ℝ))
    (fun k => ((measurable_const.sub hm).pow_const k).aestronglyMeasurable)
    (integrable_const 1) hbound hconv
  simpa only [Pi.sub_apply, integral_zero] using hi

end SlowEquilibration.DirectingPhysical
