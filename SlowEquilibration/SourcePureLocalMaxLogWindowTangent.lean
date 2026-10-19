-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureTruncatedLocalMaxDensity

/-! Logarithmic-window contact tangent for the genuine negative-Hessian pure
local-maximum Kac--Rice density. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open scoped Topology ENNReal
set_option maxHeartbeats 500000

/-- The source contact tangent applies to the actual all-critical physical
intensity along every sequence of O(log N) energy displacements. -/
theorem sourcePure_criticalPhysicalIntensity_log_window_tangent
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ)) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    Tendsto (fun n : ℕ =>
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ n)).toReal-
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E)).toReal+β*x*σ n)
      atTop (𝓝 (0 : ℝ)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  let k : ℕ → ℝ := fun n => (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hk : Tendsto k atTop (𝓝 ((p : ℝ)*E)) := by
    have hh := ((tendsto_const_nhds (x := E)).add hσzero).const_mul (p : ℝ)
    convert hh using 1
    · funext n
      dsimp [k]
      field_simp
    · ring
  have hEdgeShift : ∀ᶠ n : ℕ in atTop, 2*Real.sqrt b < k n :=
    hk.eventually (Ioi_mem_nhds hContact)
  have hBase : ∀ n : ℕ,
      (p : ℝ)*((n+2 : ℕ)*E)/(n+2 : ℕ)=(p : ℝ)*E := by
    intro n
    field_simp
  have hEq : (fun n : ℕ =>
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ n)).toReal-
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E)).toReal+β*x*σ n)
      =ᶠ[atTop] (fun n : ℕ =>
        pureActualEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n)-
          pureActualEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E)+β*x*σ n) := by
    filter_upwards [hEdgeShift] with n hn
    rw [pureCriticalPhysicalIntensity_log_shift_eq_weight n p hp a ha
      h.overlap_range.1 _ _ (hBase n ▸ hContact) hn]
  exact (sourcePure_actualEnergyLogWeight_log_window_tangent p hp a ha h hD σ hσ).congr' hEq.symm

/-- The same logarithmic contact tangent holds for the genuine
negative-Hessian pure local-maximum density, including O(log N) shifts. -/
theorem sourcePure_localMaxPhysicalIntensity_log_window_tangent
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ)) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    Tendsto (fun n : ℕ =>
      Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ n)).toReal-
      Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E)).toReal+β*x*σ n)
      atTop (𝓝 (0 : ℝ)) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let A : ℕ → ℝ := fun n =>
    (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal
  let B : ℕ → ℝ := fun n =>
    (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal
  let A₀ : ℕ → ℝ := fun n =>
    (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E)).toReal
  let B₀ : ℕ → ℝ := fun n =>
    (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E)).toReal
  have hR := sourcePure_localMaxPhysicalIntensity_div_critical_log_window
    p hp a ha h hD σ hσ
  have hR₀ := sourcePure_localMaxPhysicalIntensity_div_critical_log_window
    p hp a ha h (D := 0) (by norm_num) (fun _ => 0)
      (Filter.Eventually.of_forall (fun n => by simp))
  change Tendsto (fun n => A n/B n) atTop (𝓝 (1 : ℝ)) at hR
  have hR₀' : Tendsto (fun n => A₀ n/B₀ n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [A₀,B₀,add_zero] using hR₀
  have hLogR : Tendsto (fun n => Real.log (A n/B n)) atTop (𝓝 (0 : ℝ)) := by
    simpa [A,B] using hR.log one_ne_zero
  have hLogR₀ : Tendsto (fun n => Real.log (A₀ n/B₀ n)) atTop (𝓝 (0 : ℝ)) := by
    simpa [A₀,B₀] using hR₀'.log one_ne_zero
  have hCrit := sourcePure_criticalPhysicalIntensity_log_window_tangent
    p hp a ha h hD σ hσ
  change Tendsto (fun n => Real.log (B n)-Real.log (B₀ n)+β*x*σ n)
    atTop (𝓝 (0 : ℝ)) at hCrit
  have hTotal := (hLogR.sub hLogR₀).add hCrit
  have hEq : (fun n => Real.log (A n/B n)-Real.log (A₀ n/B₀ n)+
        (Real.log (B n)-Real.log (B₀ n)+β*x*σ n))
      =ᶠ[atTop] (fun n => Real.log (A n)-Real.log (A₀ n)+β*x*σ n) := by
    filter_upwards [hR.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hR₀'.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn hn₀
    have hB : B n ≠ 0 := by
      intro hz
      rw [hz,div_zero] at hn
      linarith
    have hA : A n ≠ 0 := by
      intro hz
      rw [hz,zero_div] at hn
      linarith
    have hB₀ : B₀ n ≠ 0 := by
      intro hz
      rw [hz,div_zero] at hn₀
      linarith
    have hA₀ : A₀ n ≠ 0 := by
      intro hz
      rw [hz,zero_div] at hn₀
      linarith
    rw [Real.log_div hA hB,Real.log_div hA₀ hB₀]
    ring
  simpa only [sub_self,zero_add,A,A₀] using hTotal.congr' hEq

end SlowEquilibration.SphericalMarkedWindows
