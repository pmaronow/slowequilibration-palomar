-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace SlowEquilibration.SphereVolume
noncomputable section
open MeasureTheory Set Metric Module
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem angular_singleton_zero (hdim : 2 ≤ Module.finrank ℝ E)
    (v : sphere (0 : E) 1) : (volume : Measure E).toSphere {v} = 0 := by
  have hvnorm : ‖(v : E)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using v.property
  have hv : (v : E) ≠ 0 := by intro h; simp [h] at hvnorm
  let line : Submodule ℝ E := Submodule.span ℝ {(v : E)}
  have hline : line ≠ ⊤ := by
    intro ht
    have hdimline : Module.finrank ℝ line = 1 := finrank_span_singleton hv
    rw [ht, finrank_top] at hdimline
    omega
  have hcone : Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : E) 1 → E) '' {v}) ⊆ line := by
    rw [image_singleton]
    intro x hx
    rcases mem_smul.mp hx with ⟨a, ha, y, hy, hxy⟩
    rw [mem_singleton_iff] at hy
    subst y
    rw [← hxy]
    exact line.smul_mem a (Submodule.subset_span (mem_singleton _))
  rw [Measure.toSphere_apply' volume (measurableSet_singleton v),
    measure_mono_null hcone (Measure.addHaar_submodule volume line hline), mul_zero]

theorem angular_noAtoms (hdim : 2 ≤ Module.finrank ℝ E) :
    NullSingletonClass ((volume : Measure E).toSphere) := ⟨angular_singleton_zero hdim⟩

theorem unitAngular_singleton_zero (hdim : 2 ≤ Module.finrank ℝ E)
    (v : sphere (0 : E) 1) : unitAngular E {v} = 0 := by
  rw [unitAngular, Measure.smul_apply, angular_singleton_zero hdim, smul_zero]

theorem unitAngular_noAtoms (hdim : 2 ≤ Module.finrank ℝ E) :
    NullSingletonClass (unitAngular E) := ⟨unitAngular_singleton_zero hdim⟩

end
end SlowEquilibration.SphereVolume
