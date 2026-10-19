-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import SlowEquilibration.ContinuousFieldPartition
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-! # The actual uniform spherical law on a genuine compact carrier -/
namespace SlowEquilibration.CompactSphereCarrier
noncomputable section
open MeasureTheory Set
open SphericalModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Carrier (d : ℕ) := ↥(Metric.closedBall (0 : Vector d) (Real.sqrt (d : ℝ)))

instance compactCarrier (d : ℕ) : CompactSpace (Carrier d) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Vector d) (Real.sqrt (d : ℝ)))

instance nonemptyCarrier (d : ℕ) : Nonempty (Carrier d) :=
  ⟨⟨0,by simpa only [Metric.mem_closedBall,dist_self] using Real.sqrt_nonneg (d : ℝ)⟩⟩

/-- Literal restriction/comap of the original normalized spherical measure. -/
def law (d : ℕ) : Measure (Carrier d) := Measure.comap Subtype.val (sphereLaw d)

lemma sphere_support_in_carrier {d : ℕ} (hd : 1 ≤ d) :
    ∀ᵐ x ∂sphereLaw d,x ∈ Metric.closedBall (0 : Vector d) (Real.sqrt (d : ℝ)) := by
  filter_upwards [sphereLaw_support hd] with x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  have he : ‖x‖=Real.sqrt (d : ℝ) :=
    (Real.sqrt_sq (norm_nonneg x)).symm.trans (congrArg Real.sqrt hx)
  exact he.le

theorem law_map_coe {d : ℕ} (hd : 1 ≤ d) :
    (law d).map (Subtype.val : Carrier d → Vector d)=sphereLaw d := by
  unfold law
  rw [map_comap_subtype_coe Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_eq_self_of_ae_mem (sphere_support_in_carrier hd)]

theorem law_probability {d : ℕ} (hd : 1 ≤ d) : IsProbabilityMeasure (law d) := by
  have hm := law_map_coe hd
  have h := congrArg (fun ν : Measure (Vector d) => ν univ) hm
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at h
  exact ⟨by simpa using h⟩

theorem integral_coe {d : ℕ} (hd : 1 ≤ d) (f : Vector d → ℝ) (hf : Measurable f) :
    (∫ x : Carrier d,f x ∂law d)=∫ x : Vector d,f x ∂sphereLaw d := by
  have hm := integral_map measurable_subtype_coe.aemeasurable
    (hf.aestronglyMeasurable (μ := (law d).map Subtype.val))
  rw [law_map_coe hd] at hm
  exact hm.symm

/-- The actual compact log-partition is exactly the original spherical
one for every globally continuous ambient field. -/
theorem logPartition_eq_sphere {d : ℕ} (hd : 1 ≤ d) (β : ℝ)
    (H : Vector d → ℝ) (hH : Continuous H) :
    ContinuousFieldPartition.logPartition (law d) β ⟨fun x => H x,hH.comp continuous_subtype_val⟩=
      Real.log (∫ x : Vector d,Real.exp (β*H x) ∂sphereLaw d) := by
  unfold ContinuousFieldPartition.logPartition ContinuousFieldPartition.partition
  congr 1
  exact integral_coe hd _ (Real.continuous_exp.comp (hH.const_mul β)).measurable

end
end SlowEquilibration.CompactSphereCarrier
