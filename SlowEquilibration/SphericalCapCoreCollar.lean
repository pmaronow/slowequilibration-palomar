-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics

@[expose] public section

/-! Actual deterministic cap, core and collar masses in Section 13. Latitude
profile controls, including a separate pole tail, are integrated using the
proved coarea law and then normalized by the actual spherical Gibbs density.
This module is the deterministic step of the good-reference proposition;
the probabilistic latitude events and likelihood transfer remain separate. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem cap_partition_eventually_le_of_latitudeProfiles {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (q₁ ρ M : ℝ),
      (∀ r ∈ Icc q₁ ρ, latitudePartitionProfile n β H u r ≤ M) →
      (∀ r ∈ Ioo ρ 1, latitudePartitionProfile n β H u r ≤ M) →
      partitionOn β H (cap u q₁) ≤ Real.exp (((n+1 : ℕ) : ℝ)*(M+ε)) := by
  filter_upwards [partitionOn_eventually_le_of_latitudeProfile_upper hε] with n hn
  intro β H hH u hu q₁ ρ M hmain hpole
  apply hn β H hH u hu (Ici q₁) measurableSet_Ici M
  intro r hr hrange
  by_cases hle : r ≤ ρ
  · exact hmain r ⟨hr,hle⟩
  · exact hpole r ⟨lt_of_not_ge hle,hrange.2⟩

theorem collar_partition_eventually_le_of_latitudeProfile {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (q₁ q₂ M : ℝ),
      (∀ r ∈ Icc q₁ q₂, latitudePartitionProfile n β H u r ≤ M) →
      partitionOn β H (collar u q₁ q₂) ≤ Real.exp (((n+1 : ℕ) : ℝ)*(M+ε)) := by
  filter_upwards [partitionOn_eventually_le_of_latitudeProfile_upper hε] with n hn
  intro β H hH u hu q₁ q₂ M hprofile
  exact hn β H hH u hu _ measurableSet_Icc M (fun r hr _ => hprofile r hr)

/-- The actual cap/core/collar restricted-partition estimates in prop:pr-good.
One dimension threshold works simultaneously for every physical field and
reference point satisfying the specified latitude profile controls. -/
theorem cap_core_collar_partitions_eventually {q w δ : ℝ} (hw : 0 < w)
    (hlo : -1 < q-w) (hhi : q+w < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (F J G q₁ q₂ ρ : ℝ),
      (∀ r ∈ Icc q₁ ρ, latitudePartitionProfile n β H u r ≤ F-J+δ/2) →
      (∀ r ∈ Ioo ρ 1, latitudePartitionProfile n β H u r ≤ F-J+δ/2) →
      (∀ r ∈ Icc (q-w) (q+w), F-J-δ/2 ≤ latitudePartitionProfile n β H u r) →
      (∀ r ∈ Icc q₁ q₂, latitudePartitionProfile n β H u r ≤ F-J-G+δ/2) →
      partitionOn β H (cap u q₁) ≤ Real.exp (((n+1 : ℕ) : ℝ)*(F-J+δ)) ∧
        Real.exp (((n+1 : ℕ) : ℝ)*(F-J-δ)) ≤ partitionOn β H (coreBand u q w) ∧
        partitionOn β H (collar u q₁ q₂) ≤ Real.exp (((n+1 : ℕ) : ℝ)*(F-J-G+δ)) := by
  filter_upwards [cap_partition_eventually_le_of_latitudeProfiles (half_pos hδ),
    coreBand_partition_eventually_ge hw hlo hhi (half_pos hδ),
    collar_partition_eventually_le_of_latitudeProfile (half_pos hδ)] with n hcap hcore hcollar
  intro β H hH u hu F J G q₁ q₂ ρ hmain hpole hband hcollarProfile
  have hc := hcap β H hH u hu q₁ ρ (F-J+δ/2) hmain hpole
  have hb := hcore β H hH u hu (F-J-δ/2) hband
  have hl := hcollar β H hH u hu q₁ q₂ (F-J-G+δ/2) hcollarProfile
  have heq1 : F-J+δ/2+δ/2=F-J+δ := by ring
  have heq2 : F-J-δ/2-δ/2=F-J-δ := by ring
  have heq3 : F-J-G+δ/2+δ/2=F-J-G+δ := by ring
  rw [heq1] at hc
  rw [heq2] at hb
  rw [heq3] at hl
  exact ⟨hc,hb,hl⟩

/-- The exact deterministic mass conclusion of prop:pr-good on the genuine
Gibbs law. The random profile and pressure events can be supplied by their
actual probabilistic theorems; no cap, core or collar mass is assumed. -/
theorem gibbsLaw_cap_core_collar_eventually_of_latitudeProfiles {q w δ : ℝ} (hw : 0 < w)
    (hlo : -1 < q-w) (hhi : q+w < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (F J G q₁ q₂ ρ : ℝ),
      |Real.log (partition (n+1) β H)/((n+1 : ℕ) : ℝ)-F| ≤ δ →
      (∀ r ∈ Icc q₁ ρ, latitudePartitionProfile n β H u r ≤ F-J+δ/2) →
      (∀ r ∈ Ioo ρ 1, latitudePartitionProfile n β H u r ≤ F-J+δ/2) →
      (∀ r ∈ Icc (q-w) (q+w), F-J-δ/2 ≤ latitudePartitionProfile n β H u r) →
      (∀ r ∈ Icc q₁ q₂, latitudePartitionProfile n β H u r ≤ F-J-G+δ/2) →
      (gibbsLaw (n+1) β H).real (cap u q₁) ≤ Real.exp (-((n+1 : ℕ) : ℝ)*(J-2*δ)) ∧
        Real.exp (-((n+1 : ℕ) : ℝ)*(J+2*δ)) ≤ (gibbsLaw (n+1) β H).real (coreBand u q w) ∧
        (gibbsLaw (n+1) β H).real (collar u q₁ q₂) ≤ Real.exp (-((n+1 : ℕ) : ℝ)*(J+G-2*δ)) := by
  filter_upwards [cap_core_collar_partitions_eventually hw hlo hhi hδ] with n hn
  intro β H hH u hu F J G q₁ q₂ ρ hp hmain hpole hband hcollarProfile
  obtain ⟨hcap,hcore,hcollar⟩ := hn β H hH u hu F J G q₁ q₂ ρ hmain hpole hband hcollarProfile
  exact gibbsLaw_cap_core_collar_bounds (by omega) β hH u hp hcap hcore hcollar

end
end SlowEquilibration.SphericalModel
