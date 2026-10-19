-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFieldKernelCongruence

/-! A Mathlib-only characterization of the physical spherical transition.
The transition is selected by its unique Cauchy problem, not by an arbitrary
spectral representative.  The proofs below identify it pointwise, including
at singular prescribed initial states, with the constructed Brownian diffusion. -/

@[expose] public section
noncomputable section

namespace SlowEquilibrationCondensedSource
open MeasureTheory Set
open scoped BigOperators Topology ContDiff NNReal

attribute [local instance] Classical.propDecidable

/-- Tangent projection on the sphere of squared radius `N`; the displayed
formula is used only at points with `inner x x = N` and `N ≥ 1`. -/
def heatProjection {N : ℕ} (x v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  v - (inner ℝ x v / (N : ℝ)) • x

/-- Ambient Riesz gradient of a real observable, with Mathlib's total
Fréchet derivative; all Cauchy-problem observables below are `C²`. -/
def heatGradient {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm (fderiv ℝ f x)

/-- Itô generator with noise `sqrt 2 P_x` and curvature drift
`-((N-1)/N)x`. On the radius-`sqrt N` sphere this is exactly
`Δ_S + β ∇_S H · ∇_S`; in particular no factor `1/2` rescales time. -/
def heatGenerator {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  fderiv ℝ f x (β • heatProjection x (heatGradient H x) -
    (((N : ℝ) - 1) / (N : ℝ)) • x) +
    (1 / 2 : ℝ) * ∑ j : Fin N,
      fderiv ℝ (fderiv ℝ f) x
        (Real.sqrt 2 • heatProjection x (EuclideanSpace.single j 1))
        (Real.sqrt 2 • heatProjection x (EuclideanSpace.single j 1))

/-- Classical backward heat evolution for a test `f` on the physical
sphere. Ambient `C²` extensions are allowed, but initial data and the PDE
are imposed on every spherical point. Joint continuity of the value and
generator includes time zero; the PDE is required at every positive real
time. Values at negative time serve only as continuous extensions. -/
def IsHeatEvolution {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  (∀ t, ContDiff ℝ 2 (u t)) ∧ Continuous (Function.uncurry u) ∧
  Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin N) => heatGenerator H β (u p.1) p.2) ∧
  (∀ x, inner ℝ x x = (N : ℝ) → u 0 x = f x) ∧
  (∀ t, 0 < t → ∀ x, inner ℝ x x = (N : ℝ) →
    HasDerivAt (fun s => u s x) (heatGenerator H β (u t) x) t)

/-- Probability-law characterization of the physical transition from a
spherical point in positive dimension. Every compactly supported `C²`
test has its unique backward Cauchy evolution on the sphere, and its
terminal integral is the value of that evolution at the initial point. This characterizes
the full probability law, including for point-mass initial data. -/
def IsTransitionLaw {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin N))
    (ν : Measure (EuclideanSpace ℝ (Fin N))) : Prop :=
  1 ≤ N ∧ inner ℝ x x = (N : ℝ) ∧ IsProbabilityMeasure ν ∧
  (∀ᵐ y ∂ν, inner ℝ y y = (N : ℝ)) ∧
  ∀ f : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∃ u, IsHeatEvolution H β f u ∧ (∫ y, f y ∂ν) = u t x

/-- The uniquely characterized Langevin transition law. Classical choice
selects a law satisfying the concrete heat Cauchy problem; existence and
uniqueness for every finite-mixture field, `N ≥ 1`, and spherical initial
point are proved in the bridge. The point mass fallback is used only when
this physical-domain characterization has no witness. It never occurs
for positive dimensions and spherical initial points; the dimension-zero
convention changes only finitely many asymptotic indices. No choice of
`L²` representative is used. -/
def transitionLaw {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin N)) : Measure (EuclideanSpace ℝ (Fin N)) :=
  if h : ∃ ν, IsTransitionLaw H β t x ν then h.choose else Measure.dirac x

end SlowEquilibrationCondensedSource

namespace SlowEquilibration.PalomarCondensed
open MeasureTheory Set Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalForm
open SphericalRotationCovariance SphericalAging.HardSphereDynamics
open scoped BigOperators Topology ContDiff NNReal

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem heatGenerator_eq {N : ℕ} (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ) :
    SlowEquilibrationCondensedSource.heatGenerator (fieldOfMixture μ J) β f =
      mixedGenerator μ J β f := rfl

private theorem physical_isHeatEvolution {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    SlowEquilibrationCondensedSource.IsHeatEvolution (fieldOfMixture μ J) β f
      (realExpectation μ J β f) := by
  refine ⟨realExpectation_contDiff μ J β hf hfc,
    realExpectation_joint_continuous μ J β hf hfc, ?_, ?_, ?_⟩
  · simpa only [heatGenerator_eq] using realExpectation_generator_joint_continuous μ J β hf hfc
  · intro x _
    exact realExpectation_zero μ J β f x
  · intro t ht x hx
    change HasDerivAt (fun s => mixedExpectation μ J β s.toNNReal f x)
      (mixedGenerator μ J β (mixedExpectation μ J β t.toNNReal f) x) t
    exact mixedExpectation_backward (by omega) μ J β x hx hf hfc t ht

private theorem generator_sub {N : ℕ} (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vector N) :
    mixedGenerator μ J β (fun y => f y - g y) x =
      mixedGenerator μ J β f x - mixedGenerator μ J β g x := by
  have hD : fderiv ℝ (fun y => f y - g y) =
      fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  have hDD : fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
    rw [hD]
    exact fderiv_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  unfold mixedGenerator Ito.coefficientGenerator SphericalAging.MultivariateTaylor.Hessian
  rw [hDD]
  simp only [hD, sub_apply, Finset.sum_sub_distrib]
  ring

private theorem heatEvolution_unique {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    {u v : ℝ → Vector N → ℝ}
    (hu : SlowEquilibrationCondensedSource.IsHeatEvolution (fieldOfMixture μ J) β f u)
    (hv : SlowEquilibrationCondensedSource.IsHeatEvolution (fieldOfMixture μ J) β f v)
    (t : ℝ) (ht : 0 ≤ t) (x : Vector N) (hx : OnSphere x) : u t x = v t x := by
  let π := mixtureGibbsLaw μ β J
  let := mixtureGibbsLaw_probability hN μ β J
  let w : ℝ → Vector N → ℝ := fun s y => u s y - v s y
  let L : ℝ → Vector N → ℝ := fun s y =>
    mixedGenerator μ J β (u s) y - mixedGenerator μ J β (v s) y
  let E : ℝ → ℝ := fun s => ∫ y, (w s y)^2 ∂π
  have hw : Continuous (Function.uncurry w) := hu.2.1.sub hv.2.1
  have hL : Continuous (Function.uncurry L) := by
    change Continuous (fun p : ℝ × Vector N => mixedGenerator μ J β (u p.1) p.2 - mixedGenerator μ J β (v p.1) p.2)
    simpa only [heatGenerator_eq, Pi.sub_apply] using! hu.2.2.1.sub hv.2.2.1
  have hwC (s : ℝ) : ContDiff ℝ 2 (w s) := (hu.1 s).sub (hv.1 s)
  have hEc : Continuous E :=
    CompactMeasure.continuous_integral π {y : Vector N | OnSphere y}
      (physicalSphere_compact N) (mixtureGibbsLaw_onSphere hN μ J β) (by
        simpa only [Function.uncurry, Pi.pow_apply] using! hw.pow 2)
  have hED (s : ℝ) (hs : 0 < s) :
      HasDerivAt E (-2 * dirichletEnergy N β (fieldOfMixture μ J) (w s)) s := by
    have hd := CompactMeasure.hasDerivAt_integral π {y : Vector N | OnSphere y}
      (physicalSphere_compact N) (mixtureGibbsLaw_onSphere hN μ J β)
      (f := fun s y => (w s y)^2) (f' := fun s y => 2 * (w s y * L s y))
      (by simpa only [Function.uncurry, Pi.pow_apply] using! hw.pow 2)
      (by simpa only [Function.uncurry, Pi.mul_apply] using! (hw.mul hL).const_mul 2)
      0 (s+1) s hs (by linarith) (by
        intro z hz y hy
        have huD := hu.2.2.2.2 z hz.1 y hy
        have hvD := hv.2.2.2.2 z hz.1 y hy
        have hh := (huD.sub hvD).pow 2
        simpa only [w, L, heatGenerator_eq, Pi.sub_apply, Pi.pow_apply,
          Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_assoc] using! hh)
    have hpair := mixedGenerator_integration_by_parts hN μ J β
      ((hwC s).of_le (by norm_num)) (hwC s)
    have heq : (∫ y, 2 * (w s y * L s y) ∂π) =
        -2 * dirichletEnergy N β (fieldOfMixture μ J) (w s) := by
      rw [integral_const_mul]
      have hsame : (∫ y, w s y * L s y ∂π) =
          ∫ y, w s y * mixedGenerator μ J β (w s) y ∂π := by
        apply integral_congr_ae
        exact .of_forall fun y => by
          dsimp only [w, L]
          rw [generator_sub μ J β (hu.1 s) (hv.1 s)]
      rw [hsame, hpair]
      unfold dirichletEnergy
      ring
    rw [heq] at hd
    exact hd
  have hanti : AntitoneOn E (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hEc.continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (hED s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hED s hs).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (dirichletEnergy_nonneg N β (fieldOfMixture μ J) (w s))
  have hE0 : E 0 = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with y hy
    simp only [w, hu.2.2.2.1 y hy, hv.2.2.2.1 y hy, sub_self, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]
  have hEt : E t = 0 := le_antisymm ((hanti (by simp) ht ht).trans_eq hE0)
    (integral_nonneg (fun _ => sq_nonneg _))
  have hi : Integrable (fun y => (w t y)^2) π :=
    integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ J).continuous
      ((hwC t).continuous.pow 2)
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (w t y)) hi).mp hEt
  have hae : w t =ᵐ[π] 0 := hz.mono fun y hy => sq_eq_zero_iff.mp hy
  have he := continuous_eq_zero_onSphere_of_gibbs_ae hN β
    (fieldOfMixture_contDiff μ J).continuous (hwC t).continuous hae x hx
  exact sub_eq_zero.mp he

/-- The actual physical transition satisfies the standalone concrete heat
Cauchy characterization. This proves the selector's witness exists. -/
theorem physical_isTransitionLaw {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    SlowEquilibrationCondensedSource.IsTransitionLaw (fieldOfMixture μ J) β t x
      (mixedTransitionKernel μ J β t x) := by
  refine ⟨hN, hx, inferInstance, ?_, ?_⟩
  · rw [mixedTransitionKernel_apply, mixedTransitionLaw]
    exact (ae_map_iff (mixedProcess_measurable μ J β x t).aemeasurable
      (sphere_measurableSet N)).mpr ((mixedProcess_onSphere (by omega) μ J β x hx).mono fun _ h => h t)
  · intro f hf hfc
    refine ⟨realExpectation μ J β f, physical_isHeatEvolution hN μ J β f hf hfc, ?_⟩
    simpa only [realExpectation, Real.toNNReal_coe] using
      (mixedExpectation_eq_kernel μ J β t f hf.continuous.stronglyMeasurable x).symm

/-- The standalone heat Cauchy characterization determines one probability
law, rather than only a Gibbs-almost-everywhere representative. -/
theorem isTransitionLaw_unique {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (x : Vector N) (hx : OnSphere x)
    (ν : Measure (Vector N))
    (hν : SlowEquilibrationCondensedSource.IsTransitionLaw (fieldOfMixture μ J) β t x ν) :
    ν = mixedTransitionKernel μ J β t x := by
  let := hν.2.2.1
  have hp := physical_isTransitionLaw hN μ J β t x hx
  apply SphericalAging.SphereSmoothTestMeasureExt.measure_eq_of_compactC2_integrals hν.2.2.2.1 hp.2.2.2.1
  intro f hf hfc
  obtain ⟨u, hu, he⟩ := hν.2.2.2.2 f hf hfc
  rw [he]
  have heq := heatEvolution_unique hN μ J β f hu (physical_isHeatEvolution hN μ J β f hf hfc)
    t t.coe_nonneg x hx
  rw [heq]
  simpa only [realExpectation, Real.toNNReal_coe] using
    mixedExpectation_eq_kernel μ J β t f hf.continuous.stronglyMeasurable x

/-- In the physical domain the concrete Cauchy characterization has exactly
one law. Thus classical selection cannot change any spherical transition. -/
theorem isTransitionLaw_existsUnique {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    ∃! ν, SlowEquilibrationCondensedSource.IsTransitionLaw (fieldOfMixture μ J) β t x ν := by
  refine ⟨_, physical_isTransitionLaw hN μ J β t x hx, ?_⟩
  intro ν hν
  exact isTransitionLaw_unique hN μ J β t x hx ν hν

/-- The selected standalone transition equals the actual Brownian Langevin
kernel at every physical initial point. The selector fallback is impossible. -/
theorem transitionLaw_eq_physical {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (x : Vector N) (hx : OnSphere x) :
    SlowEquilibrationCondensedSource.transitionLaw (fieldOfMixture μ J) β t x =
      mixedTransitionKernel μ J β t x := by
  have hex : ∃ ν, SlowEquilibrationCondensedSource.IsTransitionLaw (fieldOfMixture μ J) β t x ν :=
    ⟨_, physical_isTransitionLaw hN μ J β t x hx⟩
  rw [SlowEquilibrationCondensedSource.transitionLaw, dite_eq_left hex]
  exact isTransitionLaw_unique hN μ J β t x hx _ hex.choose_spec

end SlowEquilibration.PalomarCondensed
