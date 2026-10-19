-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureDiagonal
public import SlowEquilibration.SphericalMarkedMaximumEvents
public import SlowEquilibration.SphericalGibbsAllDimensions
public import SlowEquilibration.SourcePhysicalPairSelectionRegularity
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Analysis.Real.Sqrt

/-! Physical interfaces for source Lemma 9.22. The cap cover, its actual
Gibbs uncovered mass and its original-disorder expectation are defined below.
The fixed-deficit coarse-cover limit remains the explicit source 9.16 input;
the original maximum upper tail is the separate source 9.8 input. -/

@[expose] public section
namespace SlowEquilibration.PureCapturePhysicalDiagonalBridge
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalMarkedWindows PairConditionalDeterminantMoments
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal caps around all original critical points above the deficit. -/
def coarseCriticalCapCover (n : ℕ) (μ : FiniteMixture)
    (a e τ : ℝ) (J : Disorder (n+2) μ.maxDegree) : Set (Vector (n+2)) :=
  {x | ∃ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) ∧
    surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
    (n+2 : ℕ)*(e-τ) ≤ field (mixtureCoefficients μ) J u ∧ a ≤ overlap x u}

attribute [local irreducible] coarseCriticalCapCover

/-- A compact witness space preserves closedness of this finite-constraint
critical-point cover graph. This purely topological lemma keeps the physical
polynomial and derivative definitions outside the projection proof. -/
theorem compact_critical_cap_graph_closed
    {D V W : Type*} [TopologicalSpace D] [TopologicalSpace V]
    [TopologicalSpace W] [T2Space W] [Zero W]
    (S : Set V) (hS : IsCompact S) (g : D × V → W) (hg : Continuous g)
    (f : D × V → ℝ) (hf : Continuous f)
    (R : V × V → ℝ) (hR : Continuous R) (N a e : ℝ) :
    IsClosed {z : (D × ℝ) × V | ∃ u ∈ S,
      g (z.1.1,u) = 0 ∧ N*(e-z.1.2) ≤ f (z.1.1,u) ∧ a ≤ R (z.2,u)} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let E : Set (((D × ℝ) × V) × S) := {z |
    g (z.1.1.1,z.2.1) = 0 ∧ N*(e-z.1.1.2) ≤ f (z.1.1.1,z.2.1) ∧
      a ≤ R (z.1.2,z.2.1)}
  have hpair : Continuous (fun z : (((D × ℝ) × V) × S) => (z.1.1.1,z.2.1)) :=
    (continuous_fst.fst.fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hpair2 : Continuous (fun z : (((D × ℝ) × V) × S) => (z.1.2,z.2.1)) :=
    (continuous_fst.snd).prodMk (continuous_subtype_val.comp continuous_snd)
  have hlevel : Continuous (fun z : (((D × ℝ) × V) × S) => N*(e-z.1.1.2)) :=
    (continuous_const.sub continuous_fst.fst.snd).const_mul N
  have hE : IsClosed E :=
    (isClosed_eq (hg.comp hpair) continuous_const).inter
      ((isClosed_le hlevel (hf.comp hpair)).inter
        (isClosed_le continuous_const (hR.comp hpair2)))
  have hproj : IsClosed (Prod.fst '' E) := isClosedMap_fst_of_compactSpace E hE
  have heq : {z : (D × ℝ) × V | ∃ u ∈ S,
      g (z.1.1,u) = 0 ∧ N*(e-z.1.2) ≤ f (z.1.1,u) ∧ a ≤ R (z.2,u)} =
      Prod.fst '' E := by
    ext z
    constructor
    · rintro ⟨u,hu,hcrit,hhigh,hcap⟩
      exact ⟨(z,⟨u,hu⟩),⟨hcrit,hhigh,hcap⟩,rfl⟩
    · rintro ⟨⟨w,u⟩,hw,rfl⟩
      exact ⟨u.1,u.2,hw.1,hw.2.1,hw.2.2⟩
  rw [heq]
  exact hproj

/-- Compactness of the actual critical-point sphere makes the entire
disorder/deficit/spin cover graph closed, before integrating any Gibbs law. -/
theorem coarseCriticalCapCover_graph_isClosed (n : ℕ) (μ : FiniteMixture)
    (a e : ℝ) :
    IsClosed {z : (Disorder (n+2) μ.maxDegree × ℝ) × Vector (n+2) |
      z.2 ∈ coarseCriticalCapCover n μ a e z.1.2 z.1.1} := by
  have hR : Continuous (fun z : Vector (n+2) × Vector (n+2) => overlap z.1 z.2) := by
    unfold overlap
    exact (continuous_fst.inner continuous_snd).div_const _
  unfold coarseCriticalCapCover
  exact compact_critical_cap_graph_closed
    {u : Vector (n+2) | ‖u‖^2 = (n+2 : ℕ)} (sourceSphere_compact (n+2))
    (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) =>
      surfaceGradient (field (mixtureCoefficients μ) z.1) z.2)
    (source_surfaceGradient_joint_contDiff (mixtureCoefficients μ)).continuous
    (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) =>
      field (mixtureCoefficients μ) z.1 z.2)
    (field_jointContinuous (mixtureCoefficients μ))
    (fun z : Vector (n+2) × Vector (n+2) => overlap z.1 z.2)
    hR (n+2 : ℕ) a e

theorem coarseCriticalCapCover_measurable (n : ℕ) (μ : FiniteMixture)
    (a e τ : ℝ) (J : Disorder (n+2) μ.maxDegree) :
    MeasurableSet (coarseCriticalCapCover n μ a e τ J) :=
  by
    have hm : Measurable (fun x : Vector (n+2) => ((J,τ),x)) :=
      measurable_const.prodMk measurable_id
    change MeasurableSet ((fun x : Vector (n+2) => ((J,τ),x)) ⁻¹'
      {z : (Disorder (n+2) μ.maxDegree × ℝ) × Vector (n+2) |
        z.2 ∈ coarseCriticalCapCover n μ a e z.1.2 z.1.1})
    exact (coarseCriticalCapCover_graph_isClosed n μ a e).measurableSet.preimage hm

theorem coarseCriticalCapCover_mono (n : ℕ) (μ : FiniteMixture)
    (a e : ℝ) {τ σ : ℝ} (hτσ : τ ≤ σ)
    (J : Disorder (n+2) μ.maxDegree) :
    coarseCriticalCapCover n μ a e τ J ⊆ coarseCriticalCapCover n μ a e σ J := by
  unfold coarseCriticalCapCover
  rintro x ⟨u,hu,hcrit,hhigh,hcap⟩
  refine ⟨u,hu,hcrit,?_,hcap⟩
  have hdim : (0 : ℝ) ≤ (n+2 : ℕ) := Nat.cast_nonneg _
  nlinarith

def uncoveredGibbsMass (n : ℕ) (μ : FiniteMixture) (β a e τ : ℝ)
    (J : Disorder (n+2) μ.maxDegree) : ℝ :=
  (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).real
    (coarseCriticalCapCover n μ a e τ J)ᶜ

attribute [local irreducible] uncoveredGibbsMass

theorem uncoveredGibbsMass_joint_measurable (n : ℕ) (μ : FiniteMixture)
    (β a e : ℝ) :
    Measurable (fun p : Disorder (n+2) μ.maxDegree × ℝ =>
      uncoveredGibbsMass n μ β a e p.2 p.1) := by
  let κ : Kernel (Disorder (n+2) μ.maxDegree × ℝ) (Vector (n+2)) :=
    (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β).comap
      Prod.fst measurable_fst
  have hB : MeasurableSet
      {z : (Disorder (n+2) μ.maxDegree × ℝ) × Vector (n+2) |
        z.2 ∉ coarseCriticalCapCover n μ a e z.1.2 z.1.1} :=
    (coarseCriticalCapCover_graph_isClosed n μ a e).measurableSet.compl
  have H := (Kernel.measurable_kernel_prodMk_left (κ := κ) hB).ennreal_toReal
  simpa only [κ,uncoveredGibbsMass,Kernel.comap_apply,
    allDimensionGibbsKernel_apply,Measure.real,
    Set.preimage_ofPred_eq, Set.compl_def] using H

theorem uncoveredGibbsMass_mem_unit (n : ℕ) (μ : FiniteMixture)
    (β a e τ : ℝ) (J : Disorder (n+2) μ.maxDegree) :
    uncoveredGibbsMass n μ β a e τ J ∈ Icc (0 : ℝ) 1 := by
  let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  unfold uncoveredGibbsMass
  exact ⟨measureReal_nonneg,measureReal_le_one⟩

theorem uncoveredGibbsMass_integrable (n : ℕ) (μ : FiniteMixture)
    (β a e τ : ℝ) :
    Integrable (uncoveredGibbsMass n μ β a e τ) (disorderLaw (n+2) μ.maxDegree) := by
  have hp : Measurable (fun J : Disorder (n+2) μ.maxDegree => (J,τ)) :=
    measurable_id.prodMk measurable_const
  have hm : Measurable (uncoveredGibbsMass n μ β a e τ) :=
    (uncoveredGibbsMass_joint_measurable n μ β a e).comp hp
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro J
  rw [Real.norm_eq_abs,abs_of_nonneg (uncoveredGibbsMass_mem_unit n μ β a e τ J).1]
  exact (uncoveredGibbsMass_mem_unit n μ β a e τ J).2

def expectedUncoveredGibbsMass (n : ℕ) (μ : FiniteMixture) (β a e τ : ℝ) : ℝ :=
  ∫ J, uncoveredGibbsMass n μ β a e τ J ∂disorderLaw (n+2) μ.maxDegree

theorem expectedUncoveredGibbsMass_nonneg (n : ℕ) (μ : FiniteMixture)
    (β a e τ : ℝ) : 0 ≤ expectedUncoveredGibbsMass n μ β a e τ :=
  integral_nonneg (fun J => (uncoveredGibbsMass_mem_unit n μ β a e τ J).1)

theorem expectedUncoveredGibbsMass_antitone (n : ℕ) (μ : FiniteMixture)
    (β a e : ℝ) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    expectedUncoveredGibbsMass n μ β a e σ ≤ expectedUncoveredGibbsMass n μ β a e τ := by
  apply integral_mono (uncoveredGibbsMass_integrable n μ β a e σ)
    (uncoveredGibbsMass_integrable n μ β a e τ)
  intro J
  let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  unfold uncoveredGibbsMass
  exact measureReal_mono (μ := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J))
    (h₂ := measure_ne_top _ _)
    (compl_subset_compl.mpr (coarseCriticalCapCover_mono n μ a e hτσ J))

/-- Every original Hamiltonian value on the physical sphere lies below
its actual maximum; no Gaussian posterior or thermodynamic formula enters. -/
theorem original_field_le_sourceSphereMaximum (n : ℕ) (μ : FiniteMixture)
    (J : Disorder (n+2) μ.maxDegree) (u : Vector (n+2))
    (hu : ‖u‖^2 = (n+2 : ℕ)) :
    field (mixtureCoefficients μ) J u ≤ sourceSphereMaximum n μ 1 J := by
  obtain ⟨v,hv,_hcrit,hmax,hvalue⟩ := sourceSphereMaximum_attained n μ 1 J
  have hc : centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
    funext p
    simp [centerCoefficients]
  rw [hc] at hmax hvalue
  rw [hvalue]
  exact hmax hu

/-- On the actual maximum good event every high-energy physical point,
and hence every critical point, lies in the manuscript's diagonal window. -/
theorem high_energy_point_in_diagonal_window (n : ℕ) (μ : FiniteMixture)
    (e c : ℝ) (τ : ℕ → ℝ) (J : Disorder (n+2) μ.maxDegree)
    (hmax : sourceSphereMaximum n μ 1 J ≤
      PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ))
    (u : Vector (n+2)) (hu : ‖u‖^2 = (n+2 : ℕ))
    (hhigh : (n+2 : ℕ)*(e-τ n) ≤ field (mixtureCoefficients μ) J u) :
    field (mixtureCoefficients μ) J u ∈ Icc
      (PureCaptureDiagonal.center e c n-
        ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)))
      (PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)) := by
  rw [PureCaptureDiagonal.center_sub_deficit]
  exact ⟨hhigh,(original_field_le_sourceSphereMaximum n μ J u hu).trans hmax⟩

/-- The full physical diagonal choice, conditional only on the incoming
fixed-deficit cover conclusion. All measurability/monotonicity inputs are
discharged for the actual original field and Gibbs law. -/
theorem physical_diagonal_of_coarse_cover (μ : FiniteMixture)
    (β a e c : ℝ) (hc : 0 < c)
    (hcoarse : ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n => expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 0)) :
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      (∀ n, 1 ≤ ((n+2 : ℕ)*τ n)/(Real.log (n+2 : ℕ))^2) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => expectedUncoveredGibbsMass n μ β a e (τ n)) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) ∧
      Tendsto (fun n => ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c))/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨τ,hτpos,hfloor,hτlim,hmass,hpos,hsub,_hcenter⟩ :=
    PureCaptureDiagonal.source_pc_diagonal_core
      (fun n t => expectedUncoveredGibbsMass n μ β a e t) e c hc
      (fun n t => expectedUncoveredGibbsMass_nonneg n μ β a e t)
      (fun n t s hts => expectedUncoveredGibbsMass_antitone n μ β a e hts) hcoarse
  exact ⟨τ,hτpos,(fun n => PureCaptureDiagonal.log_floor_ratio τ n (hfloor n)),
    hτlim,hmass,hpos,hsub⟩

/-- The one-sided consequence of source maximum tightness suffices for
the growing square-root upper window. No convergence rate is supplied. -/
theorem maximum_upper_tightness_sqrt_tail_tendsto_zero (μ : FiniteMixture)
    (e c : ℝ)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ n : ℕ in atTop, (disorderLaw (n+2) μ.maxDegree).real
        {J | PureCaptureDiagonal.center e c n+L < sourceSphereMaximum n μ 1 J} ≤ ε) :
    Tendsto (fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
      {J | PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ) <
        sourceSphereMaximum n μ 1 J}) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨L,_hL,hprob⟩ := htight (ε/2) (half_pos hε)
  have hdim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hdim
  filter_upwards [hprob,hroot.eventually_gt_atTop L] with n hn hlarge
  have hsub : {J | PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ) <
      sourceSphereMaximum n μ 1 J} ⊆
      {J | PureCaptureDiagonal.center e c n+L < sourceSphereMaximum n μ 1 J} := by
    intro J hJ
    change PureCaptureDiagonal.center e c n+L < sourceSphereMaximum n μ 1 J
    change PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ) <
      sourceSphereMaximum n μ 1 J at hJ
    linarith
  have hmono := measureReal_mono (μ := disorderLaw (n+2) μ.maxDegree)
    (h₂ := measure_ne_top _ _) hsub
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  exact lt_of_le_of_lt (hmono.trans hn) (half_lt_self hε)

/-- The actual maximum-bounded event is Borel and has probability tending
to one under the one-sided source 9.8 tightness input. -/
theorem maximum_window_good_event (μ : FiniteMixture) (e c : ℝ)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ n : ℕ in atTop, (disorderLaw (n+2) μ.maxDegree).real
        {J | PureCaptureDiagonal.center e c n+L < sourceSphereMaximum n μ 1 J} ≤ ε) :
    let Ω (n : ℕ) := {J : Disorder (n+2) μ.maxDegree |
      sourceSphereMaximum n μ 1 J ≤
        PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)}
    (∀ n, MeasurableSet (Ω n)) ∧
      Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n))
        atTop (𝓝 (1 : ℝ)) := by
  dsimp only
  let Ω (n : ℕ) := {J : Disorder (n+2) μ.maxDegree |
    sourceSphereMaximum n μ 1 J ≤
      PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)}
  have hΩ (n : ℕ) : MeasurableSet (Ω n) :=
    (isClosed_le (sourceSphereMaximum_continuous n μ 1) continuous_const).measurableSet
  have hbad := maximum_upper_tightness_sqrt_tail_tendsto_zero μ e c htight
  have hsplit : (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n)) =
      (fun n => 1-(disorderLaw (n+2) μ.maxDegree).real
        {J | PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ) <
          sourceSphereMaximum n μ 1 J}) := by
    funext n
    have hadd := measureReal_add_measureReal_compl
      (μ := disorderLaw (n+2) μ.maxDegree) (hΩ n)
    rw [probReal_univ] at hadd
    have hcompl : (Ω n)ᶜ =
        {J | PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ) <
          sourceSphereMaximum n μ 1 J} := by
      ext J
      simp only [Ω,Set.mem_compl_iff,Set.mem_ofPred_eq,not_le]
    rw [hcompl] at hadd
    linarith
  refine ⟨hΩ,?_⟩
  change Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n)) _ _
  rw [hsplit]
  simpa only [sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hbad

/-- All conclusions of source 9.22 for the literal physical cover,
conditional on precisely the physical coarse-cover and one-sided maximum
tightness inputs of source 9.16 and source 9.8. The good event controls
every high-energy point, a stronger conclusion than only critical points. -/
theorem physical_diagonal_window_of_coarse_cover_and_upper_tightness
    (μ : FiniteMixture) (β a e c : ℝ) (hc : 0 < c)
    (hcoarse : ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n => expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 0))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ n : ℕ in atTop, (disorderLaw (n+2) μ.maxDegree).real
        {J | PureCaptureDiagonal.center e c n+L < sourceSphereMaximum n μ 1 J} ≤ ε) :
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      (∀ n, 1 ≤ ((n+2 : ℕ)*τ n)/(Real.log (n+2 : ℕ))^2) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => expectedUncoveredGibbsMass n μ β a e (τ n)) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) ∧
      Tendsto (fun n => ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c))/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) ∧
      ∃ Ω : (n : ℕ) → Set (Disorder (n+2) μ.maxDegree),
        (∀ n, MeasurableSet (Ω n)) ∧
        Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n))
          atTop (𝓝 (1 : ℝ)) ∧
        ∀ n J, J ∈ Ω n → ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
          (n+2 : ℕ)*(e-τ n) ≤ field (mixtureCoefficients μ) J u →
          field (mixtureCoefficients μ) J u ∈ Icc
            (PureCaptureDiagonal.center e c n-
              ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)))
            (PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)) := by
  obtain ⟨τ,hτpos,hfloor,hτlim,hmass,hpos,hsub⟩ :=
    physical_diagonal_of_coarse_cover μ β a e c hc hcoarse
  let Ω (n : ℕ) := {J : Disorder (n+2) μ.maxDegree |
    sourceSphereMaximum n μ 1 J ≤
      PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)}
  obtain ⟨hΩ,hΩlim⟩ := maximum_window_good_event μ e c htight
  refine ⟨τ,hτpos,hfloor,hτlim,hmass,hpos,hsub,Ω,hΩ,hΩlim,?_⟩
  intro n J hJ u hu hhigh
  exact high_energy_point_in_diagonal_window n μ e c τ J hJ u hu hhigh

end
end SlowEquilibration.PureCapturePhysicalDiagonalBridge
