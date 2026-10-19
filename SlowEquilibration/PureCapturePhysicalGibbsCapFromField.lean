-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalSphereCapEntropy

/-! Near-one cap bound for the original physical Gibbs law whenever the
same-disorder spherical field has a uniform linear absolute bound. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalGibbsCapFromField

open SlowEquilibration SlowEquilibration.SphericalModel
open SlowEquilibration.PureCapturePhysicalSphereCapEntropy
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
theorem gibbsLaw_mass_le_sphereLaw_of_field_bound {N : ℕ}
    (hN : 1 ≤ N) {β K : ℝ} (hβ : 0 ≤ β)
    {H : Vector N → ℝ} (hH : Continuous H)
    (hfield : ∀ x : Vector N, ‖x‖^2 = (N : ℝ) → |H x| ≤ K*(N : ℝ))
    (B : Set (Vector N)) (hB : MeasurableSet B) :
    (gibbsLaw N β H).real B ≤
      Real.exp (2*β*K*(N : ℝ))*(sphereLaw N).real B := by
  have hi : Integrable (fun x => Real.exp (β*H x)) (sphereLaw N) :=
    partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β hH
  have hupper : partitionOn β H B ≤
      Real.exp (β*K*(N : ℝ))*(sphereLaw N).real B := by
    unfold partitionOn
    calc
      _ ≤ ∫ x in B, Real.exp (β*K*(N : ℝ)) ∂sphereLaw N := by
        apply integral_mono_ae hi.integrableOn (integrable_const _)
        filter_upwards [ae_restrict_of_ae (sphereLaw_support hN)] with x hx
        exact Real.exp_le_exp.mpr (by
          have hh := (abs_le.mp (hfield x hx)).2
          nlinarith [hβ])
      _ = _ := by rw [integral_const]; simp [Measure.real, smul_eq_mul]; ring
  have hlow : Real.exp (-β*K*(N : ℝ)) ≤ partition N β H := by
    unfold partition
    calc
      Real.exp (-β*K*(N : ℝ)) =
          ∫ x, Real.exp (-β*K*(N : ℝ)) ∂sphereLaw N := by simp
      _ ≤ ∫ x, Real.exp (β*H x) ∂sphereLaw N := by
        apply integral_mono_ae (integrable_const _) hi
        filter_upwards [sphereLaw_support hN] with x hx
        exact Real.exp_le_exp.mpr (by
          have hh := (abs_le.mp (hfield x hx)).1
          nlinarith [hβ])
  rw [gibbsLaw_real_eq_partitionOn_div hN β hH hB]
  have hz : 0 < partition N β H := partition_pos hN β hH
  calc
    _ ≤ Real.exp (β*K*(N : ℝ))*(sphereLaw N).real B /
        partition N β H := div_le_div_of_nonneg_right hupper hz.le
    _ ≤ Real.exp (β*K*(N : ℝ))*(sphereLaw N).real B /
        Real.exp (-β*K*(N : ℝ)) := by
          apply div_le_div_of_nonneg_left
            (mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
            (Real.exp_pos _)
            hlow
    _ = _ := by
          have he : Real.exp (-β*K*(N : ℝ)) =
              (Real.exp (β*K*(N : ℝ)))⁻¹ := by
            rw [← Real.exp_neg]
            congr 1
            ring
          rw [div_eq_mul_inv, he, inv_inv]
          rw [show Real.exp (2*β*K*(N : ℝ)) =
            Real.exp (β*K*(N : ℝ))*Real.exp (β*K*(N : ℝ)) by
              rw [← Real.exp_add]
              congr 1
              ring]
          ring

theorem gibbsLaw_near_one_cap_bound {n : ℕ} (hn : 2 ≤ n)
    {β K : ℝ} (hβ : 0 ≤ β)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (hfield : ∀ x : Vector (n+1), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      |H x| ≤ K*((n+1 : ℕ) : ℝ))
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {a s : ℝ} (ha : 0 < a) (has : a < s) (hs : s < 1) :
    (gibbsLaw (n+1) β H).real (cap u s) ≤
      Real.exp (2*β*K*((n+1 : ℕ) : ℝ)) *
        (4*Real.sqrt (n : ℝ)*(Real.sqrt (1-a^2))^(n-2)) := by
  letI : IsProbabilityMeasure (gibbsLaw (n+1) β H) :=
    gibbsLaw_probability (by omega) β hH
  have hsub : cap u s ⊆ overlapRegion u (Ioi a) := by
    intro x hx
    exact lt_of_lt_of_le has hx
  have hmass := gibbsLaw_mass_le_sphereLaw_of_field_bound
    (by omega : 1 ≤ n+1) hβ hH hfield
    (overlapRegion u (Ioi a)) (overlapRegion_measurable u measurableSet_Ioi)
  calc
    _ ≤ (gibbsLaw (n+1) β H).real (overlapRegion u (Ioi a)) :=
      measureReal_mono hsub
    _ ≤ Real.exp (2*β*K*((n+1 : ℕ) : ℝ)) *
        (sphereLaw (n+1)).real (overlapRegion u (Ioi a)) := hmass
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sphereLaw_near_one_cap_bound hn u hu ha (lt_trans has hs))
      (Real.exp_pos _).le

end SlowEquilibration.PureCapturePhysicalGibbsCapFromField
