-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitude

/-! Exact physical overlap of two independently varying latitudes of one
pole. The transverse overlap lives on the genuine dimension-n sphere. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapMixedLatitudeOverlap
noncomputable section
open SphericalModel
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem overlap_latitude_pair_mixed {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0)
    {q₁ q₂ : ℝ} (hq₁ : |q₁| ≤ 1) (hq₂ : |q₂| ≤ 1)
    (x y : Vector n) :
    overlap (latitudeMap u e q₁ x) (latitudeMap u e q₂ y) =
      q₁*q₂+Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*overlap x y := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hN0 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq₁0 : 0 ≤ 1-q₁^2 := by nlinarith [abs_le.mp hq₁]
  have hq₂0 : 0 ≤ 1-q₂^2 := by nlinarith [abs_le.mp hq₂]
  have hratio : 0 ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ) := by positivity
  have hs₁ : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q₁^2)) =
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ))*Real.sqrt (1-q₁^2) :=
    Real.sqrt_mul hratio _
  have hs₂ : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q₂^2)) =
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ))*Real.sqrt (1-q₂^2) :=
    Real.sqrt_mul hratio _
  have hsq : (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)))^2 =
      ((n+1 : ℕ) : ℝ)/(n : ℝ) := Real.sq_sqrt hratio
  have he' : ∀ x, inner ℝ u (e x)=0 := fun x => by rw [real_inner_comm,he]
  simp only [overlap,latitudeMap,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hu,he,he',e.inner_map_map,
    mul_zero,zero_add,add_zero,hs₁,hs₂]
  calc
    _ = (q₂*(q₁*((n+1 : ℕ) : ℝ)) +
        (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)))^2*
          Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*inner ℝ x y)/
          ((n+1 : ℕ) : ℝ) := by ring
    _ = _ := by rw [hsq]; field_simp

end
end SlowEquilibration.SourcePureCapMixedLatitudeOverlap
