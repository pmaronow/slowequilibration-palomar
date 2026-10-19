-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpectralComparison
public import SlowEquilibration.SphericalReversibility

@[expose] public section

/-! # Temperature and Hamiltonian comparison with literal spherical oscillation -/
namespace SlowEquilibration.SphericalSpectralComparison
noncomputable section
open MeasureTheory Set Function
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics SphericalReversibility
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {N : ℕ}

def sphereValues (H : Vector N → ℝ) : Set ℝ := H '' {x | OnSphere x}

def sphereOscillation (H : Vector N → ℝ) : ℝ := sSup (sphereValues H)-sInf (sphereValues H)

lemma sphere_nonempty (hN : 1 ≤ N) : ({x : Vector N | OnSphere x} : Set (Vector N)).Nonempty := by
  letI := sphereLaw_probability N
  obtain ⟨x, hx⟩ := (sphereLaw_support hN).exists
  exact ⟨x, (onSphere_iff_norm_sq x).mpr hx⟩

lemma sphereValues_compact {H : Vector N → ℝ} (hH : Continuous H) : IsCompact (sphereValues H) :=
  (physicalSphere_compact N).image hH

lemma sphere_value_bounds (hN : 1 ≤ N) {H : Vector N → ℝ} (hH : Continuous H)
    (x : Vector N) (hx : OnSphere x) :
    sInf (sphereValues H) ≤ H x ∧ H x ≤ sSup (sphereValues H) := by
  have hxv : H x ∈ sphereValues H := ⟨x, hx, rfl⟩
  exact ⟨csInf_le (sphereValues_compact hH).bddBelow hxv,
    le_csSup (sphereValues_compact hH).bddAbove hxv⟩

lemma sphereOscillation_nonneg (hN : 1 ≤ N) {H : Vector N → ℝ} (hH : Continuous H) :
    0 ≤ sphereOscillation H := by
  obtain ⟨x, hx⟩ := sphere_nonempty hN
  have hb := sphere_value_bounds hN hH x hx
  exact sub_nonneg.mpr (hb.1.trans hb.2)

/-- The source temperature comparison, with the actual spherical supremum
minus infimum and exactly one exponential factor. The form eigenvalues are
constructed internally and all indices, including zero, are covered. -/
theorem temperature_eigenvalue_comparison (hN : 2 ≤ N) (β₀ β₁ : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (k : ℕ) :
    (normalizedSphericalSpectralData hN β₁ H hH.continuous).eigenvalue k ≤
      Real.exp (|β₁-β₀| *sphereOscillation H)*
        (normalizedSphericalSpectralData hN β₀ H hH.continuous).eigenvalue k := by
  let m := sInf (sphereValues H)
  let M := sSup (sphereValues H)
  by_cases hd : 0 ≤ β₁-β₀
  · have hl : ∀ x, OnSphere x → (β₁-β₀)*m ≤ β₁*H x-β₀*H x := by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left (sphere_value_bounds (by omega) hH.continuous x hx).1 hd
      dsimp [m, M]
      nlinarith
    have hu : ∀ x, OnSphere x → β₁*H x-β₀*H x ≤ (β₁-β₀)*M := by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left (sphere_value_bounds (by omega) hH.continuous x hx).2 hd
      dsimp [m, M]
      nlinarith
    have h := normalized_eigenvalue_comparison hN β₀ β₁ hH hH hl hu k
    have he : (β₁-β₀)*M-(β₁-β₀)*m = |β₁-β₀| *sphereOscillation H := by
      rw [abs_of_nonneg hd]
      dsimp [m, M, sphereOscillation]
      ring
    rw [he] at h
    exact h
  · have hd' : β₁-β₀ ≤ 0 := (lt_of_not_ge hd).le
    have hl : ∀ x, OnSphere x → (β₁-β₀)*M ≤ β₁*H x-β₀*H x := by
      intro x hx
      have hh := mul_le_mul_of_nonpos_left (sphere_value_bounds (by omega) hH.continuous x hx).2 hd'
      dsimp [m, M]
      nlinarith
    have hu : ∀ x, OnSphere x → β₁*H x-β₀*H x ≤ (β₁-β₀)*m := by
      intro x hx
      have hh := mul_le_mul_of_nonpos_left (sphere_value_bounds (by omega) hH.continuous x hx).1 hd'
      dsimp [m, M]
      nlinarith
    have h := normalized_eigenvalue_comparison hN β₀ β₁ hH hH hl hu k
    have he : (β₁-β₀)*m-(β₁-β₀)*M = |β₁-β₀| *sphereOscillation H := by
      rw [abs_of_nonpos hd']
      dsimp [m, M, sphereOscillation]
      ring
    rw [he] at h
    exact h

/-- The source Hamiltonian perturbation comparison for every actual
ordered form eigenvalue; no normalization-square loss occurs. -/
theorem hamiltonian_eigenvalue_comparison (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {H V : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (hV : ContDiff ℝ 1 V) (k : ℕ) :
    (normalizedSphericalSpectralData hN β (H+V) (hH.add hV).continuous).eigenvalue k ≤
      Real.exp (β*sphereOscillation V)*
        (normalizedSphericalSpectralData hN β H hH.continuous).eigenvalue k := by
  have hl : ∀ x, OnSphere x → β*sInf (sphereValues V) ≤ β*(H+V) x-β*H x := by
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (sphere_value_bounds (by omega) hV.continuous x hx).1 hβ
    simp only [Pi.add_apply]
    nlinarith
  have hu : ∀ x, OnSphere x → β*(H+V) x-β*H x ≤ β*sSup (sphereValues V) := by
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (sphere_value_bounds (by omega) hV.continuous x hx).2 hβ
    simp only [Pi.add_apply]
    nlinarith
  have h := normalized_eigenvalue_comparison hN β β hH (hH.add hV) hl hu k
  have he : β*sSup (sphereValues V)-β*sInf (sphereValues V)=β*sphereOscillation V := by
    unfold sphereOscillation
    ring
  rw [he] at h
  exact h

end
end SlowEquilibration.SphericalSpectralComparison
