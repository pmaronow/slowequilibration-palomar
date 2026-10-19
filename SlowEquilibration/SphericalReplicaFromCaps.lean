-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalReplicaFromTypical

/-! Uniform actual cap estimates also control both signs of two-replica overlap. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem replica_mass_le_of_uniform_caps {N : ℕ} (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν,‖x‖^2=(N:ℝ)) {s b : ℝ} (hb : 0 ≤ b)
    (hcap : ∀ v : Vector N,‖v‖^2=(N:ℝ) → ν.real (cap v s) ≤ b) :
    (ν.prod ν).real (absoluteReplicaOverlapEvent s) ≤ 2*b := by
  let T : Set (Vector N) := {x | ‖x‖^2=(N:ℝ)}
  have hT : MeasurableSet T := (isClosed_eq (continuous_id.norm.pow 2) continuous_const).measurableSet
  have hzero : ν.real Tᶜ ≤ (0:ℝ) := by
    have he : ν Tᶜ=0 := mem_ae_iff.mp hν
    simp only [measureReal_def,he,ENNReal.toReal_zero,le_refl]
  have hs (u : Vector N) (hu : u∈T) : ν.real {v | s ≤ |overlap u v|} ≤ 2*b := by
    change ‖u‖^2=(N:ℝ) at hu
    have hsub : {v : Vector N | s ≤ |overlap u v|} ⊆ cap u s ∪ cap (-u) s := by
      intro v hv
      change s ≤ |overlap u v| at hv
      rcases le_abs.mp hv with h | h
      · exact Or.inl (by simpa only [cap,mem_ofPred_eq,overlap,real_inner_comm] using h)
      · exact Or.inr (by simpa only [cap,mem_ofPred_eq,overlap,inner_neg_right,neg_div,
          real_inner_comm] using h)
    have hu' : ‖-u‖^2=(N:ℝ) := by simpa only [norm_neg] using hu
    exact (measureReal_mono hsub).trans ((measureReal_union_le (cap u s) (cap (-u) s)).trans
      (by linarith [hcap u hu,hcap (-u) hu']))
  have h := replica_mass_le_of_typical ν hT (show 0 ≤ 2*b by positivity) hzero hs
  simpa only [zero_add] using h

end SlowEquilibration.SphericalModel
