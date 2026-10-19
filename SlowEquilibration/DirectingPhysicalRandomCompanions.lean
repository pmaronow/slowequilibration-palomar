-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.DirectingPhysicalCompanions

/-! Disorder-averaged companion extraction on actual IID kernels. The
block number is chosen after averaging, so it is common to the whole
directing ensemble, as needed in the coarse-cover proof. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.DirectingPhysical

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open GaussianReplicaKernel

set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Actual query vector and k blocks of n independent replicas sampled
conditionally from the same directing measure. -/
def companionEnsembleKernel (G : Kernel Ω H) (n k : ℕ) :
    Kernel Ω (H × (Fin k → (Fin n → H))) := G ×ₖ iid (iid G n) k

instance companionEnsembleKernel_markov (G : Kernel Ω H) [IsMarkovKernel G]
    (n k : ℕ) : IsMarkovKernel (companionEnsembleKernel G n k) := by
  unfold companionEnsembleKernel
  infer_instance

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [BorelSpace H] in
theorem companionEnsembleKernel_apply (G : Kernel Ω H) [IsMarkovKernel G]
    (n k : ℕ) (ω : Ω) :
    companionEnsembleKernel G n k ω =
      (G ω).prod (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin n => G ω))) := by
  rw [companionEnsembleKernel, Kernel.prod_apply, iid_apply]
  simp_rw [iid_apply]

def companionEnsembleLaw (d : Measure Ω) (G : Kernel Ω H) (n k : ℕ) :
    Measure (H × (Fin k → (Fin n → H))) := companionEnsembleKernel G n k ∘ₘ d

instance companionEnsembleLaw_probability (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] (n k : ℕ) :
    IsProbabilityMeasure (companionEnsembleLaw d G n k) := by
  unfold companionEnsembleLaw
  infer_instance

/-- Literal event disintegration under the proved independent kernel. -/
theorem companionEnsemble_failure_real_eq_integral (d : Measure Ω)
    (G : Kernel Ω H) [IsMarkovKernel G] (n : ℕ) (Q θ : ℝ) (k : ℕ) :
    (companionEnsembleLaw d G n k).real (companionFailureEvent n Q θ k) =
      ∫ ω, (companionEnsembleKernel G n k ω).real (companionFailureEvent n Q θ k) ∂d := by
  have hE := (companionFailureEvent_closed (H := H) n Q θ k).measurableSet
  rw [companionEnsembleLaw, Measure.real, Measure.bind_apply hE
    (companionEnsembleKernel G n k).aemeasurable,
    ← integral_toReal ((companionEnsembleKernel G n k).measurable_coe hE).aemeasurable
      (.of_forall (fun ω => by finiteness))]
  rfl

/-- The actual annealed probability of failing to find a fixed number
of Q-overlap companions tends to zero, with a common block number for
the whole random directing ensemble. -/
theorem annealed_companionFailure_tendsto_zero (d : Measure Ω)
    [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (n : ℕ) {Q θ : ℝ} (hθ : 0 < θ)
    (hG : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ^ 2 = Q) :
    Tendsto (fun k => (companionEnsembleLaw d G n k).real
      (companionFailureEvent n Q θ k)) atTop (𝓝 0) := by
  simp_rw [companionEnsemble_failure_real_eq_integral]
  have hm (k : ℕ) : Measurable (fun ω =>
      (companionEnsembleKernel G n k ω).real (companionFailureEvent n Q θ k)) :=
    ((companionEnsembleKernel G n k).measurable_coe
      (companionFailureEvent_closed n Q θ k).measurableSet).ennreal_toReal
  have hb (k : ℕ) : ∀ᵐ ω ∂d,
      ‖(companionEnsembleKernel G n k ω).real (companionFailureEvent n Q θ k)‖ ≤ (1 : ℝ) :=
    .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hconv : ∀ᵐ ω ∂d, Tendsto (fun k =>
      (companionEnsembleKernel G n k ω).real (companionFailureEvent n Q θ k))
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hG] with ω hω
    simp_rw [companionEnsembleKernel_apply]
    exact companionFailure_mass_tendsto_zero (G ω) n hθ hω
  have hi := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun k => (hm k).aestronglyMeasurable) (integrable_const 1) hb hconv
  simpa only [integral_zero] using hi

end SlowEquilibration.DirectingPhysical
