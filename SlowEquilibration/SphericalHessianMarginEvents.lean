-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionMaxima

/-! Quantitative spherical Hessian margins for source `lem:pc-hessian`.
The ambient margin is exactly the intrinsic quadratic-form bound. Its
failure is a joint Borel mark, and the event imposing the margin at every
high critical point is measurable. The latter follows by projecting closed
positive-gap conditions with compact sphere and bounded direction witnesses.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalHessianMarginEvents

open MeasureTheory Set Metric
open SphericalModel SphericalForm SphereHessian PairConditionalDeterminantMoments
open SphericalAging.HardSphereDynamics
open scoped ENNReal Topology RealInnerProductSpace

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

/-- The bad-margin mark used in the determinant-weighted Kac--Rice count
for source `lem:pc-hessian`. -/
def hessianMarginFailureMark {N P : ℕ}
    (c : Degree P → ℝ) (κ : ℝ)
    (J : Disorder N P) (u : Vector N) : ℝ≥0∞ :=
  if sourceHessianMargin c κ J u then 0 else 1

/-- Every original-field critical point above the specified physical energy
threshold has the quantitative Hessian margin of source `lem:pc-hessian`. -/
def highCriticalMarginEvent (n : ℕ) (μ : FiniteMixture)
    (e τ κ : ℝ) : Set (Disorder (n+2) μ.maxDegree) :=
  {J | ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
    surfaceGradient (field (mixtureCoefficients μ) J) u = 0 →
    (n+2 : ℕ)*(e-τ) ≤ field (mixtureCoefficients μ) J u →
    sourceHessianMargin (mixtureCoefficients μ) κ J u}

/-- The all-ambient-vector margin is precisely the intrinsic Hessian bound
`∇² ≤ -κ Id` on the physical sphere. -/
theorem sourceHessianMargin_iff_intrinsic {N P : ℕ}
    (hN : 0 < N) (c : Degree P → ℝ) (J : Disorder N P)
    (u : Vector N) (hu : ‖u‖^2 = (N : ℝ)) (κ : ℝ) :
    sourceHessianMargin c κ J u ↔
      ∀ v : tangentPlane u,
        inner ℝ v (intrinsicHessian (field c J) u v) ≤ -κ*‖v‖^2 := by
  have hu' : OnSphere u := by
    simpa only [OnSphere, real_inner_self_eq_norm_sq] using hu
  have hP : ∀ v : tangentPlane u, tangentProjection u (v : Vector N) = v := by
    intro v
    rw [tangentProjection_eq_starProjection (Nat.ne_of_gt hN) u hu']
    exact (tangentPlane u).starProjection_eq_self_iff.mpr v.property
  constructor
  · intro h v
    have hv := h (v : Vector N)
    rw [hP v, ← sourceSphereHessianExtension_intrinsic_apply
      (Nat.ne_of_gt hN) c J u hu v] at hv
    exact hv
  · intro h v
    let w : tangentPlane u := (tangentPlane u).orthogonalProjectionOnto v
    have hpv : (w : Vector N) = tangentProjection u v := by
      simp only [w, Submodule.coe_orthogonalProjectionOnto_apply,
        tangentProjection_eq_starProjection (Nat.ne_of_gt hN) u hu']
    have he : sourceSphereHessianExtension c J u v =
        (intrinsicHessian (field c J) u w : Vector N) := by
      have hh := sourceSphereHessianExtension_intrinsic_apply
        (Nat.ne_of_gt hN) c J u hu w
      simp only [sourceSphereHessianExtension, ContinuousLinearMap.comp_apply, hP w] at hh
      simpa only [sourceSphereHessianExtension, ContinuousLinearMap.comp_apply, ← hpv]
        using hh.symm
    have hi : inner ℝ (w : Vector N) (intrinsicHessian (field c J) u w : Vector N) =
        inner ℝ v (intrinsicHessian (field c J) u w : Vector N) :=
      (tangentPlane u).inner_orthogonalProjectionOnto_eq_of_mem_right
        (intrinsicHessian (field c J) u w) v
    rw [he, ← hi, ← hpv]
    exact h w

/-- The failure indicator is jointly measurable in the disorder and the
sphere location, as required for marked Kac--Rice. -/
theorem hessianMarginFailureMark_measurable {N P : ℕ}
    (c : Degree P → ℝ) (κ : ℝ) :
    Measurable
      (fun z : Disorder N P × Vector N =>
        hessianMarginFailureMark c κ z.1 z.2) :=
  Measurable.ite (sourceHessianMargin_closed c κ).measurableSet
    measurable_const measurable_const

/-- A single measurable disorder event imposes the margin simultaneously
at every high spherical critical point, as in source `lem:pc-hessian`. -/
theorem highCriticalMarginEvent_measurable
    (n : ℕ) (μ : FiniteMixture) (e τ κ : ℝ) :
    MeasurableSet (highCriticalMarginEvent n μ e τ κ) := by
  let c := mixtureCoefficients μ
  let S := {u : Vector (n+2) | ‖u‖^2 = (n+2 : ℕ)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (sourceSphere_compact (n+2))
  let D := fun k : ℕ => closedBall (0 : Vector (n+2)) (k : ℝ)
  let B := {J : Disorder (n+2) μ.maxDegree | ∃ u : S,
    surfaceGradient (field c J) u = 0 ∧
    (n+2 : ℕ)*(e-τ) ≤ field c J u ∧ ¬ sourceHessianMargin c κ J u}
  -- Bounding the ambient witness avoids choosing a unit tangent vector.
  -- Every direction lies in some ball, so this preserves the exact event.
  let A := fun k m : ℕ => {z : Disorder (n+2) μ.maxDegree × (S × D k) |
    surfaceGradient (field c z.1) z.2.1 = 0 ∧
    (n+2 : ℕ)*(e-τ) ≤ field c z.1 z.2.1 ∧
    1/(m+1 : ℝ) ≤
      inner ℝ (z.2.2 : Vector (n+2))
        (sourceSphereHessianExtension c z.1 z.2.1 z.2.2) +
      κ*‖tangentProjection (z.2.1 : Vector (n+2)) z.2.2‖^2}
  have hA : ∀ k m, IsClosed (A k m) := by
    intro k m
    have hu : Continuous (fun z : Disorder (n+2) μ.maxDegree × (S × D k) =>
        (z.2.1 : Vector (n+2))) :=
      continuous_subtype_val.comp continuous_snd.fst
    have hv : Continuous (fun z : Disorder (n+2) μ.maxDegree × (S × D k) =>
        (z.2.2 : Vector (n+2))) :=
      continuous_subtype_val.comp continuous_snd.snd
    have hJu := continuous_fst.prodMk hu
    have hG := (source_surfaceGradient_joint_contDiff c).continuous.comp hJu
    have hF := (field_jointContinuous c).comp hJu
    have hH := (sourceSphereHessianExtension_joint_contDiff c).continuous.comp hJu
    have hP := (tangentProjection_continuous (n+2)).comp hu
    have hgap := (hv.inner (hH.clm_apply hv)).add
      (((hP.clm_apply hv).norm.pow 2).const_mul κ)
    exact (isClosed_eq hG continuous_const).inter
      ((isClosed_le continuous_const hF).inter (isClosed_le continuous_const hgap))
  have hImage : ∀ k m, IsClosed (Prod.fst '' A k m) := by
    intro k m
    exact isClosedMap_fst_of_compactSpace _ (hA k m)
  have hEq : B = ⋃ k : ℕ, ⋃ m : ℕ, Prod.fst '' A k m := by
    ext J
    simp only [B, mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨u, hcrit, hhigh, hbad⟩
      simp only [sourceHessianMargin, not_forall, not_le] at hbad
      obtain ⟨v, hv⟩ := hbad
      have hgap : 0 < inner ℝ v (sourceSphereHessianExtension c J u v) +
          κ*‖tangentProjection (u : Vector (n+2)) v‖^2 := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt ‖v‖
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
      have hvD : v ∈ D k := by
        simpa only [D, mem_closedBall, dist_zero_right] using hk.le
      exact ⟨k, m, (J, u, ⟨v, hvD⟩), ⟨hcrit, hhigh, hm.le⟩, rfl⟩
    · rintro ⟨k, m, ⟨J', u, v⟩, hz, rfl⟩
      have hpos : 0 < (1 : ℝ)/(m+1) := by positivity
      refine ⟨u, hz.1, hz.2.1, ?_⟩
      intro hmargin
      have hv := hmargin (v : Vector (n+2))
      have hgap := hz.2.2
      dsimp only [A] at hgap
      linarith
  have hB : MeasurableSet B := by
    rw [hEq]
    exact MeasurableSet.iUnion (fun k =>
      MeasurableSet.iUnion (fun m => (hImage k m).measurableSet))
  have hComp : highCriticalMarginEvent n μ e τ κ = Bᶜ := by
    ext J
    simp only [highCriticalMarginEvent, B, mem_ofPred_eq, mem_compl_iff]
    constructor
    · intro h ⟨u, hcrit, hhigh, hbad⟩
      exact hbad (h u u.property hcrit hhigh)
    · intro h u hu hcrit hhigh
      by_contra hbad
      exact h ⟨⟨u, hu⟩, hcrit, hhigh, hbad⟩
  rw [hComp]
  exact hB.compl

end SlowEquilibration.SphericalHessianMarginEvents
