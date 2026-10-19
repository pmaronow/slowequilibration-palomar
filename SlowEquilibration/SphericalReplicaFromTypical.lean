-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCapMass

@[expose] public section

/-! Actual replica probabilities from typical-reference estimates, for
arbitrary probability measures. -/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Fubini and the actual probability normalization give a two-replica
bound from the mass of atypical first replicas and the good section bound. -/
theorem prod_real_le_of_typical_sections {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {E : Set (X × X)} (hE : MeasurableSet E)
    {T : Set X} (hT : MeasurableSet T) {a b : ℝ} (hb : 0 ≤ b)
    (hbad : ν.real Tᶜ ≤ a) (hgood : ∀ u ∈ T, ν.real {v | (u,v) ∈ E} ≤ b) :
    (ν.prod ν).real E ≤ a+b := by
  have hsection (u : X) : ν {v | (u,v) ∈ E} ≤
      ENNReal.ofReal b + Tᶜ.indicator (fun _ => (1 : ℝ≥0∞)) u := by
    by_cases hu : u ∈ T
    · have h := hgood u hu
      have hh : ν {v | (u,v) ∈ E} ≤ ENNReal.ofReal b :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
          (by simpa only [ENNReal.toReal_ofReal hb,Measure.real] using h)
      simpa only [indicator_of_notMem (show u ∉ Tᶜ from not_not.mpr hu),add_zero] using hh
    · rw [indicator_of_mem (show u ∈ Tᶜ from hu)]
      exact (prob_le_one).trans (le_add_self)
  have he : ν.prod ν E ≤ ENNReal.ofReal b+ν Tᶜ := by
    rw [Measure.prod_apply hE]
    calc
      _ ≤ ∫⁻ u, ENNReal.ofReal b+Tᶜ.indicator (fun _ => (1 : ℝ≥0∞)) u ∂ν :=
        lintegral_mono hsection
      _ = _ := by
        rw [lintegral_add_left measurable_const,lintegral_const,lintegral_indicator hT.compl,
          setLIntegral_const,measure_univ,mul_one,one_mul]
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,measure_ne_top _ _⟩) he
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),ENNReal.toReal_ofReal hb] at hr
  change (ν.prod ν).real E ≤ b+ν.real Tᶜ at hr
  linarith

def absoluteReplicaOverlapEvent {N : ℕ} (δ : ℝ) : Set (Vector N × Vector N) :=
  {z | δ ≤ |overlap z.1 z.2|}

theorem absoluteReplicaOverlapEvent_measurable {N : ℕ} (δ : ℝ) :
    MeasurableSet (absoluteReplicaOverlapEvent (N := N) δ) := by
  unfold absoluteReplicaOverlapEvent overlap
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet

theorem replica_mass_le_of_typical {N : ℕ} (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    {T : Set (Vector N)} (hT : MeasurableSet T) {δ a b : ℝ} (hb : 0 ≤ b)
    (hbad : ν.real Tᶜ ≤ a) (hgood : ∀ u ∈ T, ν.real {v | δ ≤ |overlap u v|} ≤ b) :
    (ν.prod ν).real (absoluteReplicaOverlapEvent δ) ≤ a+b :=
  prod_real_le_of_typical_sections ν (absoluteReplicaOverlapEvent_measurable δ) hT hb hbad hgood

end SlowEquilibration.SphericalModel
