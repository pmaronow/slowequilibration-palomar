-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaKernel

/-! Ordinary transport and disintegration of the genuine finite IID
replica laws. These identify intrinsic sphere replicas with their actual
ambient unit spins without replacing the sampled Gibbs law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianReplicaKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω V W : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace W]

def mapReplicas (s : V → W) (n : ℕ) (σ : Fin n → V) : Fin n → W := fun j => s (σ j)

 theorem mapReplicas_measurable {s : V → W} (hs : Measurable s) (n : ℕ) :
    Measurable (mapReplicas s n) := Measurable.of_eval fun j => hs.comp (measurable_pi_apply j)

/-- IID replication commutes exactly with ordinary measurable transport. -/
theorem iid_map (G : Kernel Ω V) [IsMarkovKernel G] (s : V → W) (hs : Measurable s) (n : ℕ) :
    (iid G n).map (mapReplicas s n)=iid (G.map s) n := by
  let _ : IsMarkovKernel (G.map s) := Kernel.IsMarkovKernel.map G hs
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ (mapReplicas_measurable hs n),iid_apply,iid_apply]
  simp only [Kernel.map_apply G hs]
  exact Measure.pi_map_pi (fun _ => hs.aemeasurable)

/-- Ordinary disorder averaging preserves that exact transport identity. -/
theorem law_map (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    (s : V → W) (hs : Measurable s) (n : ℕ) :
    (law d G n).map (mapReplicas s n)=law d (G.map s) n := by
  rw [law,Measure.map_comp _ _ (mapReplicas_measurable hs n),iid_map G s hs n]
  rfl

 theorem mapReplicas_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G]
    (s : V → W) (hs : Measurable s) (n : ℕ) :
    HasLaw (mapReplicas s n) (law d (G.map s) n) (law d G n) where
  aemeasurable := (mapReplicas_measurable hs n).aemeasurable
  map_eq := law_map d G s hs n

/-- True replica expectations are ordinary disorder averages of the
literal conditional finite-product Gibbs expectations. -/
theorem integral_law (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    (f : (Fin n → V) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀σ,‖f σ‖≤C) :
    (∫σ,f σ ∂law d G n)=∫ω,(∫σ,f σ ∂Measure.pi (fun _ : Fin n => G ω)) ∂d := by
  have hi : Integrable f (law d G n) :=
    Integrable.of_bound hf.aestronglyMeasurable C (.of_forall hb)
  rw [law,Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  simp only [Kernel.const_apply,iid_apply]

end SlowEquilibration.GaussianReplicaKernel
