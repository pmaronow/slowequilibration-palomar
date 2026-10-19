module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalModel
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # Ordinary orthogonal Haar averaging on the physical sphere

The orthogonal group is the actual unitary subgroup of finite-dimensional
real endomorphisms. Compactness and its normalized Haar probability are
constructed, and its orbit average is compared with the literal sphere law.
-/
namespace SlowEquilibration.SphericalOrthogonalHaar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace
open SphericalModel SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal

abbrev OrthogonalGroup (N : ℕ) := unitary (Vector N →L[ℝ] Vector N)

instance orthogonalOperator_continuousStar (N : ℕ) :
    ContinuousStar (Vector N →L[ℝ] Vector N) where
  continuous_star := by
    change Continuous (ContinuousLinearMap.adjoint :
      (Vector N →L[ℝ] Vector N) → (Vector N →L[ℝ] Vector N))
    exact ContinuousLinearMap.adjoint.continuous

/-- Every genuine orthogonal endomorphism has operator norm at most one. -/
lemma orthogonal_norm_le_one {N : ℕ} (g : OrthogonalGroup N) :
    ‖(g : Vector N →L[ℝ] Vector N)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [Unitary.norm_map,one_mul]

/-- Compactness of the actual orthogonal group, from the closed unitary
equations and the unit operator ball in the finite-dimensional operator space. -/
instance orthogonalGroup_compact (N : ℕ) : CompactSpace (OrthogonalGroup N) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Vector N →L[ℝ] Vector N) 1).of_isClosed_subset isClosed_unitary
  intro g hg
  simpa only [Metric.mem_closedBall,dist_zero_right] using orthogonal_norm_le_one ⟨g,hg⟩

def leftHaar (N : ℕ) : Measure (OrthogonalGroup N) :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : PositiveCompacts (OrthogonalGroup N))

instance leftHaar_probability (N : ℕ) : IsProbabilityMeasure (leftHaar N) :=
  ⟨by unfold leftHaar; exact Measure.haarMeasure_self⟩

instance leftHaar_invariant (N : ℕ) : (leftHaar N).IsMulLeftInvariant := by
  unfold leftHaar
  infer_instance

instance leftHaar_isHaar (N : ℕ) : (leftHaar N).IsHaarMeasure := by
  unfold leftHaar
  infer_instance

/-- Compact-group Haar uniqueness proves true right invariance of the
normalized left Haar measure. -/
instance leftHaar_rightInvariant (N : ℕ) : (leftHaar N).IsMulRightInvariant := by
  constructor
  intro g
  let ν := (leftHaar N).map (fun h => h*g)
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  haveI : ν.IsMulLeftInvariant := by dsimp [ν]; infer_instance
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace ν (leftHaar N)
  have hc := congrArg (fun M : Measure (OrthogonalGroup N) => M univ) he
  simp only [measure_univ,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,mul_one] at hc
  have hc1 : Measure.haarScalarFactor ν (leftHaar N)=1 := ENNReal.coe_eq_one.mp hc.symm
  simpa only [hc1,one_smul] using he

/-- An ordinary normalized right Haar probability, constructed from the
normalized left Haar measure by group inversion. -/
def haar (N : ℕ) : Measure (OrthogonalGroup N) := (leftHaar N).inv

instance haar_probability (N : ℕ) : IsProbabilityMeasure (haar N) := by
  unfold haar
  rw [Measure.inv_def]
  infer_instance

instance haar_rightInvariant (N : ℕ) : (haar N).IsMulRightInvariant := by
  unfold haar
  infer_instance

instance haar_leftInvariant (N : ℕ) : (haar N).IsMulLeftInvariant := by
  unfold haar
  infer_instance

def action {N : ℕ} (g : OrthogonalGroup N) (x : Vector N) : Vector N :=
  (g : Vector N →L[ℝ] Vector N) x

lemma action_eq_isometry {N : ℕ} (g : OrthogonalGroup N) (x : Vector N) :
    action g x = Unitary.linearIsometryEquiv g x := rfl

lemma action_continuous (N : ℕ) : Continuous (fun q : OrthogonalGroup N × Vector N => action q.1 q.2) :=
  (continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd

lemma exists_orthogonal_map {N : ℕ} {x y : Vector N} (hn : ‖x‖=‖y‖) :
    ∃ g : OrthogonalGroup N, action g x=y := by
  let U := (ℝ ∙ (x-y))ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm U,?_⟩
  exact Submodule.reflection_sub hn

def orbitIntegral {N : ℕ} (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  ∫ g, f (action g x) ∂haar N

/-- The literal Haar orbit integral is constant on each sphere, proved by
actual transitivity and ordinary Haar right invariance. -/
theorem orbitIntegral_eq_of_norm_eq {N : ℕ} (f : Vector N → ℝ)
    {x y : Vector N} (hn : ‖x‖=‖y‖) : orbitIntegral f x=orbitIntegral f y := by
  obtain ⟨h,hh⟩ := exists_orthogonal_map hn
  rw [← hh]
  unfold orbitIntegral action
  have he : (fun g : OrthogonalGroup N => f ((g : Vector N →L[ℝ] Vector N)
      ((h : Vector N →L[ℝ] Vector N) x))) =
      fun g => f (((g*h : OrthogonalGroup N) : Vector N →L[ℝ] Vector N) x) := rfl
  rw [he]
  exact (integral_mul_right_eq_self (μ := haar N)
    (fun g : OrthogonalGroup N => f ((g : Vector N →L[ℝ] Vector N) x)) h).symm

/-- The genuine Haar orbit average of a bounded continuous test equals its
actual uniform-sphere expectation. Fubini is justified by the fixed bound. -/
theorem orbitIntegral_eq_sphere_integral {N : ℕ} (hN : 1 ≤ N)
    (f : BoundedContinuousFunction (Vector N) ℝ) (x : Vector N) (hx : OnSphere x) :
    orbitIntegral f x = ∫ y, f y ∂sphereLaw N := by
  have hc : Continuous (fun q : OrthogonalGroup N × Vector N => f (action q.1 q.2)) :=
    f.continuous.comp (action_continuous N)
  have hi : Integrable (fun q : OrthogonalGroup N × Vector N => f (action q.1 q.2))
      ((haar N).prod (sphereLaw N)) := Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable
    ‖f‖ (.of_forall fun q => f.norm_coe_le_norm (action q.1 q.2))
  have hconst : (∫ y, orbitIntegral f y ∂sphereLaw N)=orbitIntegral f x := by
    apply integral_eq_const
    filter_upwards [sphereLaw_support hN] with y hy
    have hxn := (onSphere_iff_norm_sq x).mp hx
    have hnorm : ‖y‖=‖x‖ := by nlinarith [norm_nonneg x,norm_nonneg y]
    exact orbitIntegral_eq_of_norm_eq f hnorm
  calc
    _ = ∫ y, ∫ g, f (action g y) ∂haar N ∂sphereLaw N := hconst.symm
    _ = ∫ g, ∫ y, f (action g y) ∂sphereLaw N ∂haar N := (integral_integral_swap hi).symm
    _ = ∫ y, f y ∂sphereLaw N := by
      have he (g : OrthogonalGroup N) : (∫ y, f (action g y) ∂sphereLaw N)=∫ y, f y ∂sphereLaw N := by
        change (∫ y, f (Unitary.linearIsometryEquiv g y) ∂sphereLaw N)=_
        have hm := integral_map (μ := sphereLaw N)
          (Unitary.linearIsometryEquiv g).continuous.measurable.aemeasurable
          f.continuous.stronglyMeasurable.aestronglyMeasurable
        rw [sphereLaw_rotation_invariant (Unitary.linearIsometryEquiv g)] at hm
        exact hm.symm
      simp_rw [he]
      simp

/-- The ordinary Haar average of all rotated copies of a prescribed law. -/
def average {N : ℕ} (ν : Measure (Vector N)) : Measure (Vector N) :=
  ((haar N).prod ν).map (fun q : OrthogonalGroup N × Vector N => action q.1 q.2)

instance average_probability {N : ℕ} (ν : Measure (Vector N)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (average ν) := by
  unfold average
  have hm : Measurable (fun q : OrthogonalGroup N × Vector N => action q.1 q.2) :=
    (action_continuous N).measurable
  infer_instance

/-- Source equation red-haar-average for every ordinary Borel probability
supported on the physical sphere, including singular prescribed laws. -/
theorem average_eq_sphereLaw {N : ℕ} (hN : 1 ≤ N) (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, OnSphere x) : average ν=sphereLaw N := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hc : Continuous (fun q : OrthogonalGroup N × Vector N => f (action q.1 q.2)) :=
    f.continuous.comp (action_continuous N)
  have hi : Integrable (fun q : OrthogonalGroup N × Vector N => f (action q.1 q.2))
      ((haar N).prod ν) := Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable
    ‖f‖ (.of_forall fun q => f.norm_coe_le_norm (action q.1 q.2))
  rw [average,integral_map (action_continuous N).measurable.aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable,integral_prod_symm _ hi]
  apply integral_eq_const
  filter_upwards [hν] with x hx
  exact orbitIntegral_eq_sphere_integral hN f x hx

end
end SlowEquilibration.SphericalOrthogonalHaar
