-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Compact

/-! Actual finite-dimensional images of the mixed polynomial field.
A continuous linear section removes redundant tensor coordinates. Both
full polynomial and spherical images can use this construction; the
sphere image alone is enough for Gibbs laws and physical diffusion. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalEffectiveField

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel
open scoped Topology NNReal ENNReal

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N P : ℕ}

/-- The actual mixed polynomial restricted to a compact state domain. -/
def restrictionLinear (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    Disorder N P →ₗ[ℝ] C(S, ℝ) where
  toFun J := ⟨fun x => field c J x.val, (field_contDiff c J).continuous.comp continuous_subtype_val⟩
  map_add' J K := by
    apply ContinuousMap.ext
    intro x
    change field c (J+K) x.val = field c J x.val + field c K x.val
    simpa only [fieldCLM_apply] using (fieldCLM c x.val).map_add J K
  map_smul' r J := by
    apply ContinuousMap.ext
    intro x
    change field c (r • J) x.val = r • field c J x.val
    simpa only [fieldCLM_apply] using (fieldCLM c x.val).map_smul r J

/-- Continuity follows from the actual finite tensor dimension. -/
def restrictionCLM (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    Disorder N P →L[ℝ] C(S, ℝ) := LinearMap.toContinuousLinearMap (restrictionLinear c S)

@[simp] theorem restrictionCLM_apply (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S]
    (J : Disorder N P) (x : S) : restrictionCLM c S J x = field c J x.val := rfl

/-- The actual image space, with its inherited norm topology. -/
abbrev Space (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :=
  LinearMap.range (restrictionCLM c S).toLinearMap

instance space_finiteDimensional (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    FiniteDimensional ℝ (Space c S) := LinearMap.finiteDimensional_range _

/-- Projection of genuine Gaussian tensor coefficients to their actual field. -/
def project (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    Disorder N P →L[ℝ] Space c S := (restrictionCLM c S).rangeRestrict

@[simp] theorem project_value (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S]
    (J : Disorder N P) (x : S) : (project c S J).val x = field c J x.val := rfl

/-- A continuous linear coefficient lift is constructed from surjectivity,
not postulated as a field identification assumption. -/
def lift (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    Space c S →L[ℝ] Disorder N P :=
  Classical.choose ((project c S).exists_rightInverse_of_surjective
    (restrictionCLM c S).range_rangeRestrict)

theorem project_comp_lift (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    (project c S).comp (lift c S) = ContinuousLinearMap.id ℝ (Space c S) :=
  Classical.choose_spec ((project c S).exists_rightInverse_of_surjective
    (restrictionCLM c S).range_rangeRestrict)

@[simp] theorem project_lift (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S]
    (H : Space c S) : project c S (lift c S H) = H := by
  exact congrArg (fun f : Space c S →L[ℝ] Space c S => f H) (project_comp_lift c S)

/-- The chosen lift represents the same literal field at every point of its domain. -/
theorem field_lift (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S]
    (H : Space c S) (x : S) : field c (lift c S H) x.val = H.val x := by
  have h := congrArg (fun h : Space c S => h.val x) (project_lift c S H)
  exact h

/-- The actual effective field law, with no tensor coordinate retained. -/
def law (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] : Measure (Space c S) :=
  (disorderLaw N P).map (project c S)

instance law_probability (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    IsProbabilityMeasure (law c S) := by
  unfold law
  exact (Measure.isProbabilityMeasure_map_iff (project c S).measurable.aemeasurable).mpr inferInstance

/-- This law is the genuine Gaussian linear image of the original mixed tensor law. -/
theorem project_hasGaussianLaw (c : Degree P → ℝ) (S : Set (Vector N)) [CompactSpace S] :
    HasGaussianLaw (project c S) (disorderLaw N P) :=
  (disorder_hasGaussianLaw N P).map_fun (project c S)

/-- Compact ball containing the physical sphere and a nonempty open neighborhood of zero. -/
def fieldBall (N : ℕ) : Set (Vector N) := Metric.closedBall 0 (Real.sqrt N + 1)

instance fieldBall_compactSpace (N : ℕ) : CompactSpace (fieldBall N) := by
  unfold fieldBall
  infer_instance

/-- Actual physical spherical restriction domain. -/
def fieldSphere (N : ℕ) : Set (Vector N) := Metric.sphere 0 (Real.sqrt N)

instance fieldSphere_compactSpace (N : ℕ) : CompactSpace (fieldSphere N) := by
  unfold fieldSphere
  infer_instance

abbrev FullSpace (c : Degree P → ℝ) := Space c (fieldBall N)
abbrev SphereSpace (c : Degree P → ℝ) := Space c (fieldSphere N)

theorem mem_fieldSphere_iff (x : Vector N) : x ∈ fieldSphere N ↔ ‖x‖^2=(N:ℝ) := by
  simp only [fieldSphere, Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h
    rw [h, Real.sq_sqrt (Nat.cast_nonneg N)]
  · intro h
    rw [← h, Real.sqrt_sq (norm_nonneg x)]

theorem mem_fieldBall_of_norm_sq (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    x ∈ fieldBall N := by
  have hnorm : ‖x‖ = Real.sqrt (N:ℝ) := by
    rw [← hx, Real.sqrt_sq (norm_nonneg x)]
  simp only [fieldBall, Metric.mem_closedBall, dist_zero_right, hnorm]
  linarith

/-- The canonical full-field lift agrees at every actual spherical point. -/
theorem full_lift_project_on_sphere (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    field c (lift c (fieldBall N) (project c (fieldBall N) J)) x = field c J x := by
  exact field_lift c (fieldBall N) (project c (fieldBall N) J)
    ⟨x, mem_fieldBall_of_norm_sq x hx⟩

/-- The spherical lift also agrees exactly on its original sphere. -/
theorem sphere_lift_project_on_sphere (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    field c (lift c (fieldSphere N) (project c (fieldSphere N) J)) x = field c J x := by
  exact field_lift c (fieldSphere N) (project c (fieldSphere N) J)
    ⟨x, (mem_fieldSphere_iff x).mpr hx⟩

end SlowEquilibration.SphericalEffectiveField
