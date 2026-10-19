-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiSphereNetGeometry
public import Mathlib.Tactic

/-! Finite deterministic nets for the physical center sphere of squared
radius `N Q`, in the normalization used by Subag's replicated bands. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCaptureReplicaNetGeometry
noncomputable section

open Set Filter SphericalParisiSphereNet
open SphericalAging.FiniteModel PureTensorJetBounds
open scoped Topology
set_option autoImplicit false

/-- A deterministic finite net of the center sphere. Its size is exponential
in `N` with exactly the usual Euclidean covering entropy, so a fixed replica
count can beat the union bound before `N → ∞`. -/
theorem exists_physical_center_net
    (N : ℕ) (hN : 0 < N) {Q θ : ℝ} (hQ : 0 < Q) (hθ : 0 < θ) :
    ∃ (k : ℕ) (points : Fin k → Vector N), 0 < k ∧
      (∀ j, ‖points j‖ = Real.sqrt (N : ℝ) * Real.sqrt Q) ∧
      (∀ m : Vector N,
        ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt Q →
          ∃ j, ‖m - points j‖ ≤ θ * Real.sqrt (N : ℝ)) ∧
      Real.log (k : ℝ) ≤
        (N : ℝ) * Real.log (1 + 2 * Real.sqrt Q / θ) := by
  let s : ℝ := Real.sqrt (N : ℝ) * Real.sqrt Q
  have hsN : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hs : 0 < s := mul_pos hsN hsQ
  let ε : ℝ := θ / Real.sqrt Q
  have hε : 0 < ε := div_pos hθ hsQ
  obtain ⟨k,u,hk,hu,hcard⟩ := exists_unitSphere_net hN hε
  let points : Fin k → Vector N := fun j => s • (u j).val
  refine ⟨k,points,hk,?_,?_,?_⟩
  · intro j
    dsimp only [points]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    have hun : ‖(u j).val‖ = 1 := by
      simpa only [PureTensorJetBounds.UnitSphere, Metric.mem_sphere,
        dist_zero_right] using (u j).property
    simp only [hun,mul_one]
    rfl
  · intro m hm
    let v : UnitSphere N := ⟨s⁻¹ • m, by
      have hvnorm : ‖s⁻¹ • m‖ = 1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),hm]
        exact inv_mul_cancel₀ hs.ne'
      simpa only [PureTensorJetBounds.UnitSphere, Metric.mem_sphere,
        dist_zero_right] using hvnorm⟩
    obtain ⟨j,hj⟩ := hu v
    refine ⟨j,?_⟩
    have hscale : s • (s⁻¹ • m) = m := by
      rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    have heq : m - points j = s • (v.val - (u j).val) := by
      dsimp only [points,v]
      rw [smul_sub,hscale]
    rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    calc
      s * ‖v.val - (u j).val‖ ≤ s * ε :=
        mul_le_mul_of_nonneg_left hj hs.le
      _ = θ * Real.sqrt (N : ℝ) := by
        dsimp [s,ε]
        field_simp [hsQ.ne']
  · convert hcard using 1
    congr 2
    dsimp [ε]
    field_simp [hθ.ne',hsQ.ne']

end
end SlowEquilibration.SourcePureCaptureReplicaNetGeometry
