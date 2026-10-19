-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalGeodesicDecay
public import Mathlib.Topology.Order.IntermediateValue

/-! Deterministic localization of strict spherical superlevel components,
as in manuscript `lem:pc-superlevel`. A component has a critical maximizer;
the covariant third-derivative bound and the high-critical Hessian margin
confine the entire component to a short geodesic ball with a unique critical
point and the quantitative energy-deficit radius. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalSuperlevelLocalization

open Set Filter SphericalModel SphericalGaussianJet SphericalForm
open PairConditionalDeterminantMoments SphericalCriticalGeodesicDecay
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology RealInnerProductSpace

set_option autoImplicit false

private theorem mem_component_of_mem_closure {E : Type*} [TopologicalSpace E]
    {U : Set E} {w u : E} (hw : w ∈ U) (hu : u ∈ U)
    (hcl : u ∈ closure (connectedComponentIn U w)) :
    u ∈ connectedComponentIn U w := by
  rw [connectedComponentIn_eq_image hw] at hcl ⊢
  have hucomp := (Topology.IsInducing.subtypeVal.isClosed_iff'.mp
    (isClosed_connectedComponent (x := (⟨w, hw⟩ : U)))) (⟨u, hu⟩ : U) hcl
  exact ⟨⟨u, hu⟩, hucomp, rfl⟩

private theorem component_curve_localMax {E : Type*} [TopologicalSpace E]
    (f : E → ℝ) (U : Set E) (u : E)
    (hmax : IsMaxOn f (connectedComponentIn U u) u)
    (γ : ℝ → E) (hγ : Continuous γ) (hγ0 : γ 0 = u)
    (hγU : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U) :
    IsLocalMax (fun t => f (γ t)) 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hγU
  have hballpre : IsPreconnected (Metric.ball (0 : ℝ) ε) := by
    rw [Real.ball_eq_Ioo]
    exact isPreconnected_Ioo
  have hpre : IsPreconnected (γ '' Metric.ball (0 : ℝ) ε) :=
    hballpre.image γ hγ.continuousOn
  have huim : u ∈ γ '' Metric.ball (0 : ℝ) ε := by
    rw [← hγ0]
    exact mem_image_of_mem γ (Metric.mem_ball_self hε)
  have hsub : γ '' Metric.ball (0 : ℝ) ε ⊆ connectedComponentIn U u :=
    hpre.subset_connectedComponentIn huim (by
      rintro x ⟨t, ht, rfl⟩
      exact hball ht)
  change ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f (γ 0)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  rw [hγ0]
  exact hmax (hsub (mem_image_of_mem γ ht))

private theorem component_maximum_critical {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (J : Disorder N P) (a : ℝ)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hhigh : a < field c J u)
    (hmax : IsMaxOn (field c J)
      (connectedComponentIn {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < field c J x} u) u) :
    surfaceGradient (field c J) u = 0 := by
  have hu' : OnSphere u := by
    simpa only [OnSphere, real_inner_self_eq_norm_sq] using hu
  have hdir (v : Vector N) (hv : inner ℝ u v = 0) : fderiv ℝ (field c J) u v = 0 := by
    let A := tangentRotation u v
    have hA : star A = -A := tangentRotation_skew u v
    have hAu : A u = v := tangentRotation_apply hN.ne' u v hu' hv
    have hcurve := operatorFlow_apply_hasDerivAt A 0 u
    have hcont : Continuous (fun t : ℝ => operatorFlow A t u) :=
      (operatorFlow_continuous A).clm_apply continuous_const
    have hcomp := ((field_contDiff c J).differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hcurve
        (show u = operatorFlow A 0 u from (operatorFlow_zero A u).symm)
    have hγU : ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖operatorFlow A t u‖ ^ 2 = (N : ℝ) ∧ a < field c J (operatorFlow A t u) := by
      have hh : ∀ᶠ t in 𝓝 (0 : ℝ), a < field c J (operatorFlow A t u) :=
        (isOpen_lt continuous_const ((field_contDiff c J).continuous.comp hcont)).mem_nhds
          (by simpa only [mem_ofPred_eq, Function.comp_apply, operatorFlow_zero] using hhigh)
      filter_upwards [hh] with t ht
      exact ⟨by rw [operatorFlow_norm A hA t u]; exact hu, ht⟩
    have hlocal := component_curve_localMax (field c J) _ u hmax
      (fun t => operatorFlow A t u) hcont (operatorFlow_zero A u) hγU
    simpa only [Function.comp_def, operatorFlow_zero, hAu] using
      hlocal.hasDerivAt_eq_zero hcomp
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient, inner_zero_left]
  apply hdir
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    (tangentProjection_mem hN.ne' u v hu')

private theorem component_has_critical_maximum {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (J : Disorder N P) (a : ℝ)
    (w : Vector N) (hw : ‖w‖ ^ 2 = (N : ℝ)) (hhigh : a < field c J w) :
    ∃ u ∈ connectedComponentIn
      {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < field c J x} w,
      surfaceGradient (field c J) u = 0 ∧
      ∀ z ∈ connectedComponentIn
        {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < field c J x} w,
        field c J z ≤ field c J u := by
  let U := {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < field c J x}
  let V := connectedComponentIn U w
  have hwU : w ∈ U := ⟨hw, hhigh⟩
  have hwV : w ∈ V := mem_connectedComponentIn hwU
  have hclS : closure V ⊆ {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)} :=
    closure_minimal (fun x hx => (connectedComponentIn_subset U w hx).1)
      (sourceSphere_compact N).isClosed
  have hcompact : IsCompact (closure V) :=
    (sourceSphere_compact N).of_isClosed_subset isClosed_closure hclS
  obtain ⟨u, hucl, hmax⟩ := hcompact.exists_isMaxOn
    ⟨w, subset_closure hwV⟩ (field_contDiff c J).continuous.continuousOn
  have huU : u ∈ U := ⟨hclS hucl, hhigh.trans_le (hmax (subset_closure hwV))⟩
  have huV : u ∈ V := mem_component_of_mem_closure hwU huU hucl
  have hmaxV : IsMaxOn (field c J) V u := fun z hz => hmax (subset_closure hz)
  have hcrit : surfaceGradient (field c J) u = 0 := by
    apply component_maximum_critical hN c J a u huU.1 huU.2
    rwa [← connectedComponentIn_eq huV]
  exact ⟨u, huV, hcrit, hmaxV⟩

private theorem field_short_ball_quadratic_drop {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u w : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hw : ‖w‖ ^ 2 = (N : ℝ))
    (hCrit : surfaceGradient (field c J) u = 0)
    (hMargin : sourceHessianMargin c κ J u)
    (hDist : sphereGeodesicDist u w ≤ ρ * Real.sqrt (N : ℝ)) :
    field c J w ≤ field c J u - κ / 4 * (sphereGeodesicDist u w) ^ 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  by_cases heq : w = u
  · subst w
    simp [sphereGeodesicDist, overlap_self (by omega) u hu]
  have hNpos : 0 < n + 1 := by omega
  have hsqrt : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  have hr := overlap_mem_Icc_of_norm_sq hNpos u w hu hw
  have hrlt : overlap u w < 1 := lt_of_le_of_ne hr.2 (by
    intro he
    exact heq (source_sphere_eq_of_overlap_one hNpos u w hu hw he).symm)
  have hθpos : 0 < Real.arccos (overlap u w) := Real.arccos_pos.mpr hrlt
  have hθle : Real.arccos (overlap u w) ≤ ρ := by
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    simpa only [sphereGeodesicDist, mul_comm] using hDist
  have hθone := hθle.trans hρ1
  have hrpos : 0 < overlap u w := by
    rw [← Real.cos_arccos hr.1 hr.2]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  obtain ⟨v, hv, huv, hEnd⟩ := sourceSphereGeodesic_reconstruction u w hu hw ⟨hrpos, hrlt⟩
  have H := field_geodesic_quadratic_drop hN c J hC hκ hρ hρ1 hρκ hThird
    u v hu hv huv hCrit hMargin (Real.arccos (overlap u w)) ⟨hθpos.le, hθle⟩
  rw [hEnd] at H
  convert H using 1
  unfold sphereGeodesicDist
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

/-- Source `lem:pc-superlevel`: every strict high-energy component has a
unique critical maximizer and lies within both the curvature radius and
the radius determined by its energy deficit. -/
theorem field_superlevel_component_localization {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ δ₀ δ : ℝ}
    (hC : 0 < C) (hκ : 0 < κ) (hδ₀ : 0 < δ₀) (hδ : 0 < δ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ)) :
    let S := {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)}
    let f := field c J
    let M := sSup (f '' S)
    let ρ := min (1 : ℝ) (κ / (2 * C))
    (∀ u ∈ S, surfaceGradient f u = 0 →
      M - δ₀ * (N : ℝ) < f u → sourceHessianMargin c κ J u) →
    δ < min δ₀ (κ * ρ ^ 2 / 4) →
    ∀ w ∈ S, M - δ * (N : ℝ) < f w →
      let V := connectedComponentIn
        {x : Vector N | x ∈ S ∧ M - δ * (N : ℝ) < f x} w
      ∃ u ∈ V,
        surfaceGradient f u = 0 ∧
        sourceHessianMargin c κ J u ∧
        (∀ z ∈ V, f z ≤ f u) ∧
        (∀ z ∈ V, surfaceGradient f z = 0 → z = u) ∧
        (∀ z ∈ V,
          sphereGeodesicDist u z < ρ * Real.sqrt (N : ℝ) ∧
          sphereGeodesicDist u z <
            2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ)) := by
  intro S f M ρ hMargins hsmall w hw hhigh
  let V := connectedComponentIn {x : Vector N | x ∈ S ∧ M - δ * (N : ℝ) < f x} w
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega : 0 < N)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hκ (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρκ : 2 * C * ρ ≤ κ := by
    have hh : ρ ≤ κ / (2 * C) := min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hh
  have hδδ₀ : δ < δ₀ := hsmall.trans_le (min_le_left _ _)
  have hδρ : δ < κ * ρ ^ 2 / 4 := hsmall.trans_le (min_le_right _ _)
  have hVsub : V ⊆ {x : Vector N | x ∈ S ∧ M - δ * (N : ℝ) < f x} :=
    connectedComponentIn_subset _ _
  obtain ⟨u, huV, hcrit, hmax⟩ := component_has_critical_maximum (by omega) c J
    (M - δ * (N : ℝ)) w hw hhigh
  have huS : u ∈ S := (hVsub huV).1
  have hMargin : sourceHessianMargin c κ J u := hMargins u huS hcrit (by
    have hh := (hVsub huV).2
    have hd := mul_lt_mul_of_pos_right hδδ₀ hNr
    have hδ₀N := mul_pos hδ₀ hNr
    linarith [hδ₀N])
  have huM : f u ≤ M := le_csSup
    ((sourceSphere_compact N).image (field_contDiff c J).continuous).bddAbove ⟨u, huS, rfl⟩
  have hdist : Continuous (sphereGeodesicDist u) := by
    unfold sphereGeodesicDist overlap
    fun_prop
  have hdist0 : sphereGeodesicDist u u = 0 := by
    simp [sphereGeodesicDist, overlap_self (by omega) u huS]
  have hball : ∀ z ∈ V, sphereGeodesicDist u z < ρ * Real.sqrt (N : ℝ) := by
    intro z hz
    by_contra hh
    have hge : ρ * Real.sqrt (N : ℝ) ≤ sphereGeodesicDist u z := le_of_not_gt hh
    obtain ⟨y, hy, hdy⟩ := isPreconnected_connectedComponentIn.intermediate_value
      huV hz hdist.continuousOn (show ρ * Real.sqrt (N : ℝ) ∈
        Icc (sphereGeodesicDist u u) (sphereGeodesicDist u z) from
          ⟨by rw [hdist0]; positivity, hge⟩)
    have hdrop := field_short_ball_quadratic_drop hN c J hC hκ hρ hρ1 hρκ hThird
      u y huS (hVsub hy).1 hcrit hMargin hdy.le
    rw [hdy, mul_pow, Real.sq_sqrt hNr.le] at hdrop
    have hhhigh := (hVsub hy).2
    have hd := mul_lt_mul_of_pos_right hδρ hNr
    change f y ≤ f u - κ / 4 * (ρ ^ 2 * (N : ℝ)) at hdrop
    nlinarith
  refine ⟨u, huV, hcrit, hMargin, hmax, ?_, ?_⟩
  · intro z hz hzcrit
    exact field_short_ball_critical_unique hN c J hC hκ hρ hρ1 hρκ hThird
      u z huS (hVsub hz).1 hcrit hMargin hzcrit (hball z hz).le
  · intro z hz
    refine ⟨hball z hz, ?_⟩
    have hdrop := field_short_ball_quadratic_drop hN c J hC hκ hρ hρ1 hρκ hThird
      u z huS (hVsub hz).1 hcrit hMargin (hball z hz).le
    have hhhigh := (hVsub hz).2
    have hsq : (sphereGeodesicDist u z) ^ 2 < 4 * (δ / κ) * (N : ℝ) := by
      apply (mul_lt_mul_iff_of_pos_right hκ).mp
      have heq : (4 * (δ / κ) * (N : ℝ)) * κ = 4 * δ * (N : ℝ) := by
        field_simp
      rw [heq]
      change f z ≤ f u - κ / 4 * (sphereGeodesicDist u z) ^ 2 at hdrop
      nlinarith
    have hrad : 0 < 2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ) := by positivity
    have hradsq : (2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ)) ^ 2 =
        4 * (δ / κ) * (N : ℝ) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt (div_pos hδ hκ).le]
      norm_num
    rw [← hradsq] at hsq
    nlinarith [sq_nonneg (sphereGeodesicDist u z -
      2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ))]

end SlowEquilibration.SphericalSuperlevelLocalization
