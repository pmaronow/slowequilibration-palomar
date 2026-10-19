-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeRegularity

@[expose] public section

/-!
# A concrete finite mesh of the latitude interval

The mesh has exactly k+1 indexed points. Its covering radius is proved from
the ordinary floor function, so later Gaussian union bounds use a literal
finite family of latitude partitions.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeMeshPoint (k : ℕ) (a b : ℝ) (i : Fin (k+1)) : ℝ :=
  a+(b-a)*(i.val : ℝ)/(k : ℝ)

theorem latitudeMeshPoint_mem {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a ≤ b)
    (i : Fin (k+1)) : latitudeMeshPoint k a b i ∈ Icc a b := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hi : (i.val : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show i.val ≤ k by omega)
  have hn : 0 ≤ (b-a)*(i.val : ℝ)/(k : ℝ) := by positivity
  have hu : (b-a)*(i.val : ℝ)/(k : ℝ) ≤ b-a := by
    apply (div_le_iff₀ hk0).mpr
    exact mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab)
  exact ⟨by dsimp [latitudeMeshPoint]; linarith,by dsimp [latitudeMeshPoint]; linarith⟩

/-- Every latitude lies within the stated distance of an actual indexed
mesh point, uniformly including the two interval endpoints. -/
theorem latitudeMeshPoint_covers {k : ℕ} (hk : 1 ≤ k) {a b q : ℝ}
    (hab : a ≤ b) (hq : q ∈ Icc a b) :
    ∃ i : Fin (k+1), |q-latitudeMeshPoint k a b i| ≤ (b-a)/(k : ℝ) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  rcases eq_or_lt_of_le hab with rfl | hab
  · have hqa : q=a := by linarith [hq.1,hq.2]
    subst q
    exact ⟨⟨0,by omega⟩,by simp [latitudeMeshPoint]⟩
  · let t : ℝ := (k : ℝ)*(q-a)/(b-a)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (mul_nonneg hk0.le (sub_nonneg.mpr hq.1)) (sub_pos.mpr hab).le
    have htk : t ≤ (k : ℝ) := by
      dsimp [t]
      apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
      nlinarith [hq.2]
    have hfloor : ⌊t⌋₊ ≤ k := Nat.floor_le_of_le htk
    let i : Fin (k+1) := ⟨⌊t⌋₊,by omega⟩
    refine ⟨i,?_⟩
    have he : q-latitudeMeshPoint k a b i = (b-a)/(k : ℝ)*(t-(⌊t⌋₊ : ℝ)) := by
      dsimp [latitudeMeshPoint,i,t]
      field_simp
      ring
    rw [he,abs_mul,abs_of_pos (div_pos (sub_pos.mpr hab) hk0)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Nat.abs_sub_floor_le ht0)
      (div_pos (sub_pos.mpr hab) hk0).le

end SlowEquilibration.SphericalModel
