-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.C1SphericalGraph
public import SlowEquilibration.SphericalLaplace
public import SlowEquilibration.GraphLaplace

@[expose] public section

/-!
# Actual Langevin trajectories in the completed spherical form domain

The graph representative uses the literal mixed transition expectation and
its genuine rotation derivatives. The continuity, energy bounds, and weak
evolution equation are derived from the physical SDE and Gibbs integration
by parts.
-/

noncomputable section
namespace SlowEquilibration.SphericalLaplaceIdentification

open MeasureTheory Filter Set
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology InnerProductSpace ContDiff NNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine jointly continuous representatives give a continuous trajectory
in actual Gibbs L², using the actual compact sphere support. -/
theorem gibbsToL2_joint_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (f : ℝ → Vector N → ℝ) (hf : Continuous (Function.uncurry f)) :
    Continuous (fun t => gibbsToL2 hN β H hH (f t)
      (hf.comp (continuous_const.prodMk continuous_id))) := by
  have : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have hI : Continuous (fun t => ∫ x, (f t x-f t₀ x)^2 ∂gibbsLaw N β H) :=
    CompactMeasure.continuous_integral (gibbsLaw N β H)
      {x : Vector N | OnSphere x} (physicalSphere_compact N)
      ((gibbsLaw_support hN β H).mono (fun x hx => (onSphere_iff_norm_sq x).mpr hx))
      ((hf.sub (hf.comp (continuous_const.prodMk continuous_snd))).pow 2)
  have ht : Tendsto (fun t => ∫ x, (f t x-f t₀ x)^2 ∂gibbsLaw N β H)
      (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]
      using hI.tendsto t₀
  have hnorm (t : ℝ) :
      ‖gibbsToL2 hN β H hH (f t) (hf.comp (continuous_const.prodMk continuous_id)) -
        gibbsToL2 hN β H hH (f t₀) (hf.comp (continuous_const.prodMk continuous_id))‖ ^ 2 =
      ∫ x, (f t x-f t₀ x)^2 ∂gibbsLaw N β H := by
    rw [← gibbsToL2_sub, ← real_inner_self_eq_norm_sq, gibbsToL2_inner]
    simp only [Pi.sub_apply, pow_two]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    (ht.congr' (.of_forall (fun t => (hnorm t).symm)))
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

variable {N : ℕ}

abbrev potential (μ : FiniteMixture) (J : Disorder N μ.maxDegree) : Vector N → ℝ :=
  fieldOfMixture μ J

lemma potential_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    Continuous (potential μ J) := (fieldOfMixture_contDiff μ J).continuous

def trajectory (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) : sphericalSobolevGraph hN β (potential μ J) (potential_continuous μ J) :=
  C1ToGraph hN β (potential μ J) (potential_continuous μ J)
    (realExpectation μ J β f t)
    ((realExpectation_contDiff μ J β hf hfc t).of_le (by norm_num))

theorem trajectory_L2 (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) :
    sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
      (trajectory hN μ J β f hf hfc t) =
    SphericalL2Semigroup.P hN μ J β t.toNNReal
      (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous) := by
  apply Lp.ext
  filter_upwards [gibbsToL2_coe hN β (potential μ J) (potential_continuous μ J)
    (realExpectation μ J β f t) (realExpectation_contDiff μ J β hf hfc t).continuous,
    SphericalL2Semigroup.P_ae_expectation hN μ J β t.toNNReal
      (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous)
      hf.continuous.stronglyMeasurable
      (gibbsToL2_coe hN β (potential μ J) (potential_continuous μ J) f hf.continuous)]
    with x hx hy
  exact hx.trans hy.symm

theorem trajectory_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (trajectory hN μ J β f hf hfc) := by
  have hv := gibbsToL2_joint_continuous hN β (potential μ J) (potential_continuous μ J)
    (realExpectation μ J β f) (realExpectation_joint_continuous μ J β hf hfc)
  have hmap : Continuous (fun q : ℝ × Vector N => (q.1.toNNReal, q.2)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  have hD := (mixedExpectation_regular μ J β hf hfc).2.2.1.comp hmap
  have hrot : Continuous (fun (t : ℝ) (ij : Fin N × Fin N) =>
      gibbsToL2 hN β (potential μ J) (potential_continuous μ J)
        (lieDerivative (coordinateRotation ij.1 ij.2) (realExpectation μ J β f t))
        (lieDerivative_continuous _
          ((realExpectation_contDiff μ J β hf hfc t).of_le (by norm_num)))) := by
    apply continuous_pi
    intro ij
    apply gibbsToL2_joint_continuous
    exact hD.clm_apply ((coordinateRotation ij.1 ij.2).continuous.comp continuous_snd)
  have hpi := ((PiLp.homeomorph 2
    (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β (potential μ J)))).symm.continuous).comp hrot
  have hn := hpi.const_smul (gradientScale N)
  apply Continuous.subtype_mk
  exact ((WithLp.homeomorphProd 2 _ _).symm.continuous).comp (hv.prodMk hn)

/-- The genuine smooth graph is dense in its actual completion. -/
theorem smoothEnergyToGraph_dense (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    DenseRange (smoothEnergyToGraph hN β H hH) := by
  apply Metric.denseRange_iff.mpr
  intro z r hr
  have hm : z.val ∈ closure (Set.range (smoothGradientGraphLinear hN β H hH)) := z.property
  obtain ⟨a, ⟨f, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hm r hr
  exact ⟨f, ha⟩

lemma mixedGenerator_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {g : Vector N → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (mixedGenerator μ J β g) :=
  Ito.generator_continuous β (mixedGradient μ J) (mixedGradient_contDiff μ J) hg

def generatorVector (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (g : Vector N → ℝ) (hg : ContDiff ℝ 2 g) : SphericalL2Semigroup.Space μ J β :=
  gibbsToL2 hN β (potential μ J) (potential_continuous μ J)
    (mixedGenerator μ J β g) (mixedGenerator_continuous μ J β hg)

/-- Actual generator integration by parts extends from the genuine smooth
core to every member of the completed graph. -/
theorem C2_graph_generator_pairing (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (g : Vector N → ℝ) (hg : ContDiff ℝ 2 g)
    (v : sphericalSobolevGraph hN β (potential μ J) (potential_continuous μ J)) :
    sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J)
      (C1ToGraph hN β (potential μ J) (potential_continuous μ J) g (hg.of_le (by norm_num))) v =
      -inner ℝ (generatorVector hN μ J β g hg)
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v) := by
  apply (smoothEnergyToGraph_dense hN β (potential μ J) (potential_continuous μ J)).induction_on
    (p := fun v => sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J)
      (C1ToGraph hN β (potential μ J) (potential_continuous μ J) g (hg.of_le (by norm_num))) v =
      -inner ℝ (generatorVector hN μ J β g hg)
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v)) v
  · exact isClosed_eq
      (continuous_const.inner (sphericalEnergyGradientMap hN β (potential μ J)
        (potential_continuous μ J)).continuous)
      ((continuous_const.inner (sphericalEnergyL2Map hN β (potential μ J)
        (potential_continuous μ J)).continuous).neg)
  · intro w
    change sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J)
      (C1ToGraph hN β (potential μ J) (potential_continuous μ J) g (hg.of_le (by norm_num)))
      (C1ToGraph hN β (potential μ J) (potential_continuous μ J) w
        ((smoothCore_contDiff w).of_le (by simp))) = _
    rw [sphericalCompletedDirichlet_C1, dirichletForm_symmetric]
    have hb := rotationGenerator_integration_by_parts hN β
      ((fieldOfMixture_contDiff μ J).of_le (by simp))
      ((smoothCore_contDiff w).of_le (by simp)) hg
    have hi : inner ℝ (generatorVector hN μ J β g hg)
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
          (smoothEnergyToGraph hN β (potential μ J) (potential_continuous μ J) w)) =
        ∫ x, (w : Vector N → ℝ) x * rotationGenerator N β (potential μ J) g x
          ∂gibbsLaw N β (potential μ J) := by
      change inner ℝ
        (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) (mixedGenerator μ J β g)
          (mixedGenerator_continuous μ J β hg))
        (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) w
          (smoothCore_contDiff w).continuous) = _
      rw [gibbsToL2_inner]
      apply integral_congr_ae
      filter_upwards [gibbsLaw_support hN β (potential μ J)] with x hx
      rw [mixedGenerator_eq_rotationGenerator (by omega) μ J β hg x
        ((onSphere_iff_norm_sq x).mpr hx), mul_comm]
    rw [hi]
    linarith

/-- The actual generator applied to the genuine transition expectation is
the transition applied to the original generator, in actual Gibbs L². -/
theorem trajectory_generatorVector (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ) :
    generatorVector hN μ J β (realExpectation μ J β f t)
      (realExpectation_contDiff μ J β hf hfc t) =
    SphericalL2Semigroup.P hN μ J β t.toNNReal (generatorVector hN μ J β f hf) := by
  apply Lp.ext
  filter_upwards [gibbsToL2_coe hN β (potential μ J) (potential_continuous μ J)
      (mixedGenerator μ J β (realExpectation μ J β f t))
      (mixedGenerator_continuous μ J β (realExpectation_contDiff μ J β hf hfc t)),
    SphericalL2Semigroup.P_ae_expectation hN μ J β t.toNNReal
      (generatorVector hN μ J β f hf)
      (mixedGenerator_continuous μ J β hf).stronglyMeasurable
      (gibbsToL2_coe hN β (potential μ J) (potential_continuous μ J)
        (mixedGenerator μ J β f) (mixedGenerator_continuous μ J β hf)),
    gibbsLaw_support hN β (potential μ J)] with x hx hy hs
  change (generatorVector hN μ J β (realExpectation μ J β f t)
    (realExpectation_contDiff μ J β hf hfc t)) x = _ at hx
  rw [hx, hy]
  by_cases ht : 0 < t
  · exact mixedExpectation_generator_commutes (by omega) μ J β x
      ((onSphere_iff_norm_sq x).mpr hs) hf hfc t ht
  · have ht' : t.toNNReal = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_gt ht)
    have he : realExpectation μ J β f t = f := by
      funext y
      simpa only [realExpectation, ht', Real.toNNReal_zero] using realExpectation_zero μ J β f y
    rw [he, ht']
    simpa only [realExpectation, Real.toNNReal_zero] using
      (realExpectation_zero μ J β (mixedGenerator μ J β f) x).symm

/-- The genuine completed graph norm is uniformly bounded along a compact
C² Langevin observable. The actual energy follows from Gibbs integration by
parts and the proved L² contraction for both f and its generator. -/
theorem trajectory_bounded (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖trajectory hN μ J β f hf hfc t‖ ≤ C := by
  let U := gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous
  let V := generatorVector hN μ J β f hf
  refine ⟨‖U‖ + ‖V‖ + 1, by positivity, ?_⟩
  intro t
  let z := trajectory hN μ J β f hf hfc t
  let A := sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
  have hu : ‖A z‖ ≤ ‖U‖ := by
    rw [show A z = SphericalL2Semigroup.P hN μ J β t.toNNReal U from
      trajectory_L2 hN μ J β f hf hfc t]
    exact SphericalL2Semigroup.P_apply_norm_le hN μ J β t.toNNReal U
  have he := C2_graph_generator_pairing hN μ J β (realExpectation μ J β f t)
    (realExpectation_contDiff μ J β hf hfc t) z
  rw [trajectory_generatorVector hN μ J β f hf hfc t] at he
  change sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J) z z =
    -inner ℝ (SphericalL2Semigroup.P hN μ J β t.toNNReal V) (A z) at he
  have hg : sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J) z z ≤
      ‖U‖ * ‖V‖ := by
    rw [he]
    calc
      _ ≤ |inner ℝ (SphericalL2Semigroup.P hN μ J β t.toNNReal V) (A z)| := neg_le_abs _
      _ ≤ ‖SphericalL2Semigroup.P hN μ J β t.toNNReal V‖ * ‖A z‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖V‖ * ‖U‖ := mul_le_mul
        (SphericalL2Semigroup.P_apply_norm_le hN μ J β t.toNNReal V) hu
        (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hn := sphericalCompletedDirichlet_add_L2 hN β (potential μ J)
    (potential_continuous μ J) z z
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg U)).mpr hu
  have hsq : ‖z‖ ^ 2 ≤ (‖U‖ + ‖V‖ + 1) ^ 2 := by
    nlinarith [norm_nonneg U, norm_nonneg V]
  exact (sq_le_sq₀ (norm_nonneg z) (by positivity)).mp hsq

/-- Differentiation against an arbitrary integrable Gibbs weight. Only the
actual compact support and genuine continuous value/derivative jets are used;
the weight itself need not have a smooth representative. -/
theorem weighted_hasDerivAt_integral (ν : Measure (Vector N)) [IsFiniteMeasure ν]
    (K : Set (Vector N)) (hK : IsCompact K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    {F F' : ℝ → Vector N → ℝ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (w : Vector N → ℝ) (hw : Integrable w ν)
    (a b z : ℝ) (ha : a < z) (hb : z < b)
    (hd : ∀ t ∈ Ioo a b, ∀ x ∈ K, HasDerivAt (fun s => F s x) (F' t x) t) :
    HasDerivAt (fun t => ∫ x, F t x*w x ∂ν) (∫ x, F' z x*w x ∂ν) z := by
  let l := (a+z)/2
  let u := (z+b)/2
  have hl : a < l := by dsimp [l]; linarith
  have hu : u < b := by dsimp [u]; linarith
  have hs : Icc l u ∈ 𝓝 z := Icc_mem_nhds (by dsimp [l]; linarith) (by dsimp [u]; linarith)
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc l u)).prod hK).bddAbove_image
    hF'.norm.continuousOn
  have hfz : Continuous (F z) := hF.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfz.continuousOn
  have hi : Integrable (fun x => F z x*w x) ν := by
    apply (hw.norm.const_mul C).mono'
      ((hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul hw.aestronglyMeasurable)
    filter_upwards [hν] with x hx
    change ‖F z x*w x‖ ≤ C*‖w x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := fun t x => F t x*w x) (F' := fun t x => F' t x*w x)
    (bound := fun x => M*‖w x‖) (x₀ := z) (s := Icc l u) hs
    (Eventually.of_forall (fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul hw.aestronglyMeasurable)) hi
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (by
      filter_upwards [hν] with x hx t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM ⟨(t,x), ⟨ht,hx⟩, rfl⟩) (norm_nonneg _))
    (hw.norm.const_mul M)
    (hν.mono (fun x hx t ht =>
      (hd t ⟨hl.trans_le ht.1, ht.2.trans_lt hu⟩ x hx).mul_const (w x)))).2

theorem gibbsToL2_inner_arbitrary (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (g : Vector N → ℝ) (hg : Continuous g)
    (W : Lp ℝ 2 (gibbsLaw N β H)) :
    inner ℝ (gibbsToL2 hN β H hH g hg) W = ∫ x, g x*W x ∂gibbsLaw N β H := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gibbsToL2_coe hN β H hH g hg] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The actual SDE backward equation holds against every vector of actual
Gibbs L², including all completed graph test functions. -/
theorem realExpectation_inner_hasDerivAt (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (W : SphericalL2Semigroup.Space μ J β) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => inner ℝ
      (gibbsToL2 hN β (potential μ J) (potential_continuous μ J)
        (realExpectation μ J β f s) (realExpectation_contDiff μ J β hf hfc s).continuous) W)
      (inner ℝ (generatorVector hN μ J β (realExpectation μ J β f t)
        (realExpectation_contDiff μ J β hf hfc t)) W) t := by
  have : IsProbabilityMeasure (mixtureGibbsLaw μ β J) := mixtureGibbsLaw_probability hN μ β J
  have hd := weighted_hasDerivAt_integral (mixtureGibbsLaw μ β J)
    {x : Vector N | OnSphere x} (physicalSphere_compact N)
    (mixtureGibbsLaw_onSphere hN μ J β)
    (F := realExpectation μ J β f)
    (F' := fun s => mixedGenerator μ J β (realExpectation μ J β f s))
    (realExpectation_joint_continuous μ J β hf hfc)
    (realExpectation_generator_joint_continuous μ J β hf hfc)
    (W : Vector N → ℝ) ((Lp.memLp W).integrable (by norm_num))
    0 (t+1) t ht (by linarith)
    (fun s hs x hx => mixedExpectation_backward (by omega) μ J β x hx hf hfc s hs.1)
  convert hd using 1
  · funext s
    exact gibbsToL2_inner_arbitrary hN β (potential μ J) (potential_continuous μ J)
      (realExpectation μ J β f s) (realExpectation_contDiff μ J β hf hfc s).continuous W
  · exact gibbsToL2_inner_arbitrary hN β (potential μ J) (potential_continuous μ J)
      (mixedGenerator μ J β (realExpectation μ J β f t))
      (mixedGenerator_continuous μ J β (realExpectation_contDiff μ J β hf hfc t)) W

/-- The actual Langevin graph trajectory satisfies the genuine completed
form weak evolution equation. No generator extension is assumed. -/
theorem trajectory_weak_evolution (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (v : sphericalSobolevGraph hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => inner ℝ
      (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
        (trajectory hN μ J β f hf hfc s))
      (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v))
      (-(inner ℝ (trajectory hN μ J β f hf hfc t) v -
        inner ℝ (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
          (trajectory hN μ J β f hf hfc t))
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v))) t := by
  have hd := realExpectation_inner_hasDerivAt hN μ J β f hf hfc
    (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v) t ht
  have he := C2_graph_generator_pairing hN μ J β (realExpectation μ J β f t)
    (realExpectation_contDiff μ J β hf hfc t) v
  have hb := sphericalCompletedDirichlet_add_L2 hN β (potential μ J)
    (potential_continuous μ J) (trajectory hN μ J β f hf hfc t) v
  change sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J)
      (trajectory hN μ J β f hf hfc t) v = _ at he
  change HasDerivAt (fun s => inner ℝ
      (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
        (trajectory hN μ J β f hf hfc s))
      (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v))
      (inner ℝ (generatorVector hN μ J β (realExpectation μ J β f t)
        (realExpectation_contDiff μ J β hf hfc t))
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v)) t at hd
  have hc : inner ℝ (generatorVector hN μ J β (realExpectation μ J β f t)
        (realExpectation_contDiff μ J β hf hfc t))
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v) =
      -(inner ℝ (trajectory hN μ J β f hf hfc t) v -
        inner ℝ (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
          (trajectory hN μ J β f hf hfc t))
        (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) v)) := by linarith
  rw [hc] at hd
  exact hd

/-- The literal Langevin Laplace operator equals the independently
constructed genuine spherical weak resolvent on every compact C² observable. -/
theorem R_eq_form_on_compact_C2 (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    SphericalLaplace.R hN μ J β
      (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous) =
    sphericalL2Resolvent hN β (potential μ J) (potential_continuous μ J)
      (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous) := by
  obtain ⟨C, hC, hb⟩ := trajectory_bounded hN μ J β f hf hfc
  have h := GraphLaplace.image_integral_eq_resolvent
    (sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J))
    (trajectory hN μ J β f hf hfc) (trajectory_continuous hN μ J β f hf hfc)
    C (fun t _ => hb t) (trajectory_weak_evolution hN μ J β f hf hfc)
  have hz : sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
      (trajectory hN μ J β f hf hfc 0) =
      gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous := by
    rw [trajectory_L2, Real.toNNReal_zero, SphericalL2Semigroup.P_zero]
    rfl
  rw [hz] at h
  have hi : (fun t : ℝ => Real.exp (-t) •
      sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J)
        (trajectory hN μ J β f hf hfc t)) =
      (fun t : ℝ => Real.exp (-t) • SphericalL2Semigroup.P hN μ J β t.toNNReal
        (gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous)) := by
    funext t
    rw [trajectory_L2]
  rw [hi] at h
  exact h

/-- Exact identification on the whole actual Gibbs Hilbert space, derived
by the proved density of genuine compact smooth observables. -/
theorem R_eq_form (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) :
    SphericalLaplace.R hN μ J β =
      sphericalL2Resolvent hN β (potential μ J) (potential_continuous μ J) := by
  apply ContinuousLinearMap.ext
  intro U
  have hc : IsClosed {U | SphericalLaplace.R hN μ J β U =
      sphericalL2Resolvent hN β (potential μ J) (potential_continuous μ J) U} :=
    isClosed_eq (SphericalLaplace.R hN μ J β).continuous
      (sphericalL2Resolvent hN β (potential μ J) (potential_continuous μ J)).continuous
  apply (SphericalL2Semigroup.smoothCore_dense hN μ J β).induction
    (P := fun U => SphericalLaplace.R hN μ J β U =
      sphericalL2Resolvent hN β (potential μ J) (potential_continuous μ J) U) ?_ hc U
  rintro U ⟨f, hUf, hfc, hf⟩
  have he : U = gibbsToL2 hN β (potential μ J) (potential_continuous μ J) f hf.continuous := by
    apply Lp.ext
    exact hUf.trans (gibbsToL2_coe hN β (potential μ J) (potential_continuous μ J) f hf.continuous).symm
  rw [he]
  exact R_eq_form_on_compact_C2 hN μ J β f (hf.of_le (by simp)) hfc

end SlowEquilibration.SphericalLaplaceIdentification
