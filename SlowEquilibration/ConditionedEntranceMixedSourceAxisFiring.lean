-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceGibbsFiniteFiring
public import SlowEquilibration.SphericalJointSpatialGradient
public import SlowEquilibration.SphericalSmoothParameterProcess
public import SlowEquilibration.SphericalJointGibbsKernel

/-! Jointly measurable Brownian firing representatives for physical source axes. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalSmoothParameter
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics FeynmanKac
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The finite firing mass built from the jointly measurable physical
Brownian representative is itself measurable in axis, spin, and noise. -/
theorem jointAxis_finiteDiscountedMass_stronglyMeasurable
    {N : ℕ} (β : ℝ) (g : (Vector N × Vector N) → Vector N)
    (hg : ContDiff ℝ 1 g) (κ : (Vector N × Vector N) → ℝ)
    (hκ : Measurable κ) (θ : ℝ) (L : ℝ≥0) :
    let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
        (Vector N × Vector N) := fun t q =>
      (q.1.1, jointProcess β g hg q.1 t q.2)
    StronglyMeasurable (finiteDiscountedMass κ Y θ L) := by
  dsimp only
  let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
      (Vector N × Vector N) := fun t q =>
    (q.1.1, jointProcess β g hg q.1 t q.2)
  have hp : Measurable (fun z : ℝ≥0 × ((Vector N × Vector N) × VectorBrownian.Space N) =>
      ((z.2.1,z.1),z.2.2)) := by fun_prop
  have hu : Measurable (fun z : ℝ≥0 × ((Vector N × Vector N) × VectorBrownian.Space N) =>
      z.2.1.1) := by fun_prop
  have hY : Measurable (Function.uncurry Y) :=
    hu.prodMk ((jointProcess_measurable β g hg).comp hp)
  exact finiteDiscountedMass_stronglyMeasurable κ hκ Y hY θ L

/-- A moving Gibbs initial state can integrate the bounded Brownian
firing representative measurably over spin and physical axis. -/
theorem jointAxis_gibbs_finiteDiscountedMass_mean_measurable
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : (Vector N × Vector N) → ℝ) (hH : Continuous H)
    (g : (Vector N × Vector N) → Vector N) (hg : ContDiff ℝ 1 g)
    (κ : (Vector N × Vector N) → ℝ) (hκ : Measurable κ)
    (θ : ℝ) (L : ℝ≥0) :
    let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
        (Vector N × Vector N) := fun t q =>
      (q.1.1, jointProcess β g hg q.1 t q.2)
    Measurable (fun u : Vector N =>
      ∫ x, ∫ omega, finiteDiscountedMass κ Y θ L ((u,x),omega)
        ∂VectorBrownian.law N ∂gibbsLaw N β (fun y => H (u,y))) := by
  dsimp only
  let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
      (Vector N × Vector N) := fun t q =>
    (q.1.1, jointProcess β g hg q.1 t q.2)
  have hf : StronglyMeasurable (finiteDiscountedMass κ Y θ L) :=
    jointAxis_finiteDiscountedMass_stronglyMeasurable β g hg κ hκ θ L
  have hfbar : StronglyMeasurable (fun q : Vector N × Vector N =>
      ∫ omega, finiteDiscountedMass κ Y θ L (q,omega)
        ∂VectorBrownian.law N) :=
    hf.integral_prod_right'
  exact jointHamiltonian_integral_measurable hN β H hH _ hfbar

/-- At each fixed physical axis and initial spin, the jointly measurable
Brownian representative gives the actual spherical gradient process for
almost every Brownian path. -/
theorem jointAxis_finiteDiscountedMass_ae_actual
    {N : ℕ} (β : ℝ) (g : (Vector N × Vector N) → Vector N)
    (hg : ContDiff ℝ 1 g) (κ : (Vector N × Vector N) → ℝ)
    (θ : ℝ) (L : ℝ≥0) (u x : Vector N) :
    let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
        (Vector N × Vector N) := fun t q =>
      (q.1.1, jointProcess β g hg q.1 t q.2)
    ∀ᵐ omega ∂VectorBrownian.law N,
      finiteDiscountedMass κ Y θ L ((u,x),omega) =
      finiteDiscountedMass (fun y => κ (u,y))
        (SphericalC1Dynamics.process β (fun y => g (u,y))
          (hg.comp (contDiff_const.prodMk contDiff_id)) x) θ L omega := by
  dsimp only
  let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
      (Vector N × Vector N) := fun t q =>
    (q.1.1, jointProcess β g hg q.1 t q.2)
  filter_upwards [jointProcess_ae_actual β g hg (u,x)] with omega homega
  unfold finiteDiscountedMass survival occupation
  simp_rw [homega]

private theorem mixedSourceAxisHamiltonian_contDiff
    {N : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (J : Disorder N μ.maxDegree)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (e k : ℝ) :
    ContDiff ℝ 2 (fun z : Vector N × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
  (sourceSmoothCutoffField_jointContDiff μ Q hQ hnp α χ hχ).comp
    (show ContDiff ℝ 2 (fun z : Vector N × Vector N =>
      ((J,(z.1,(e,k))),z.2)) by fun_prop)

theorem mixedSourceAxisGradient_contDiff
    {N : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (J : Disorder N μ.maxDegree)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (e k : ℝ) :
    ContDiff ℝ 1 (jointSpatialGradient (fun z : Vector N × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2)) :=
  jointSpatialGradient_contDiff _
    (mixedSourceAxisHamiltonian_contDiff μ hQ hnp J α χ hχ e k)

/-- The moving source-Gibbs Brownian firing mean has a measurable
representative for the literal fixed-disorder mixed source cutoff. -/
theorem mixedSource_axis_finiteDiscountedMass_mean_measurable
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (β α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (e k θ : ℝ) (L : ℝ≥0) :
    let H : Vector N × Vector N → ℝ := fun z =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2
    let g := jointSpatialGradient H
    let hg := mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k
    let κ : Vector N × Vector N → ℝ := fun z => capKilling α z.1 z.2
    let Y : ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
        (Vector N × Vector N) := fun t q =>
      (q.1.1, jointProcess β g hg q.1 t q.2)
    Measurable (fun u : Vector N =>
      ∫ x, ∫ omega, finiteDiscountedMass κ Y θ L ((u,x),omega)
        ∂VectorBrownian.law N ∂gibbsLaw N β (fun y => H (u,y))) := by
  dsimp only
  let H : Vector N × Vector N → ℝ := fun z =>
    sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2
  have hH : ContDiff ℝ 2 H :=
    mixedSourceAxisHamiltonian_contDiff μ hQ hnp J α χ hχ e k
  let g := jointSpatialGradient H
  let hg := mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k
  let κ : Vector N × Vector N → ℝ := fun z => capKilling α z.1 z.2
  have hrc : Continuous (fun z : Vector N × Vector N => overlapValue z.1 z.2) := by
    simpa only [overlapValue_eq] using
      (continuous_inner (𝕜 := ℝ) (E := Vector N)).div_const (N : ℝ)
  have hκ : Continuous κ := by
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc.neg)
  exact jointAxis_gibbs_finiteDiscountedMass_mean_measurable hN β H hH.continuous
    g hg κ hκ.measurable θ L

/-- The jointly measurable source path varies over the physical axis;
at the stored axis it is a representative of the actual SourceData path. -/
def sourceData_axisJointProcess {N : ℕ} (D : SmoothKilled.SourceData N) (β : ℝ) :
    ℝ≥0 → ((Vector N × Vector N) × VectorBrownian.Space N) →
      (Vector N × Vector N) :=
  let H : Vector N × Vector N → ℝ := fun z =>
    sourceSmoothCutoffField D.mixture D.Q D.Q_pos D.nonpure D.disorder z.1
      D.energyMark D.radialMark D.cutoffScale D.cutoff z.2
  let g := jointSpatialGradient H
  let hg := mixedSourceAxisGradient_contDiff D.mixture D.Q_pos D.nonpure D.disorder
    D.cutoffScale D.cutoff D.cutoff_smooth D.energyMark D.radialMark
  fun t q => (q.1.1, jointProcess β g hg q.1 t q.2)

/-- The measurable axis process gives the literal Brownian source firing
mass at the stored physical axis, almost surely in the Brownian noise. -/
theorem sourceData_axisJoint_finiteDiscountedMass_ae_actual
    {N : ℕ} (D : SmoothKilled.SourceData N) (β θ : ℝ) (L : ℝ≥0)
    (x : Vector N) :
    ∀ᵐ omega ∂VectorBrownian.law N,
      finiteDiscountedMass (fun z : Vector N × Vector N =>
        capKilling D.cutoffScale z.1 z.2) (sourceData_axisJointProcess D β)
        θ L ((D.axis,x),omega) =
      finiteDiscountedMass (capKilling D.cutoffScale D.axis)
        (SmoothKilled.process D β x) θ L omega := by
  let H : Vector N × Vector N → ℝ := fun z =>
    sourceSmoothCutoffField D.mixture D.Q D.Q_pos D.nonpure D.disorder z.1
      D.energyMark D.radialMark D.cutoffScale D.cutoff z.2
  let g := jointSpatialGradient H
  let hg := mixedSourceAxisGradient_contDiff D.mixture D.Q_pos D.nonpure D.disorder
    D.cutoffScale D.cutoff D.cutoff_smooth D.energyMark D.radialMark
  let κ : Vector N × Vector N → ℝ := fun z => capKilling D.cutoffScale z.1 z.2
  have h := jointAxis_finiteDiscountedMass_ae_actual β g hg κ θ L D.axis x
  filter_upwards [h, SmoothKilled.process_ae_actual D β x] with omega homega hp
  convert homega using 1
  · rfl
  · unfold finiteDiscountedMass survival occupation
    simp_rw [hp]
    rfl

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
