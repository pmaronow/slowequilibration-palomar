-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandUpperExtraction
public import SlowEquilibration.SphericalLatitudeLaplace
public import SlowEquilibration.SourceLiteratureParisiTemperatureEven

/-!
# Subag's quenched band upper approximation

The transverse direction of the actual uniform sphere, restricted to any
measurable set of axial overlaps, has exactly its original uniform angular
law multiplied by the mass of that restriction. This identifies the
projected one-factor partition without annealing the Taylor remainder.
Projection to the exact latitude and the replica mean bound then prove
`ExpectedBandUpperApproximation` with its original quantifiers. Gaussian
disorder symmetry includes every real temperature. No literature hypothesis
is needed beyond the limits already encoded in the thermodynamic data.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandUpperFinal

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagRemark25Proof LiteratureSubagBandUpperExtraction
open SphericalTaylorRemainder SphericalPairCommonFrame SphericalGaussianJet
open WholeFieldRegression
open scoped Topology BigOperators ENNReal RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem planeDirection_measurable {N : ℕ} (u : Vector N) :
    Measurable (planeDirection u) := by
  unfold planeDirection planeScale overlap
  fun_prop

/-- Normalizing a latitude's transverse component removes its axial
coordinate, including the finite-dimensional radius correction. -/
theorem planeDirection_latitudeMap {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1))
    (he : ∀ x, inner ℝ (e x) u = 0)
    {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) (x : Vector n) :
    planeDirection u (latitudeMap u e a x) =
      (Real.sqrt (n : ℝ))⁻¹ • e x := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have harg : 0 < 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
  have hov : overlap u (latitudeMap u e a x) = a := by
    rw [show overlap u (latitudeMap u e a x) = overlap (latitudeMap u e a x) u from
      by unfold overlap; rw [real_inner_comm]]
    exact overlap_latitude_center u hu e he a x
  let S := Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - a ^ 2))
  let T := Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ) * (1 - a ^ 2))
  have hS : 0 < S := Real.sqrt_pos.mpr (mul_pos (by positivity) harg)
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hscalar0 : T * Real.sqrt (n : ℝ) = S := by
    apply (sq_eq_sq₀ (by dsimp [T]; positivity) hS.le).mp
    dsimp [T, S]
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnR.le,
      Real.sq_sqrt (by positivity)]
    field_simp
  have hscalar : S⁻¹ * T = (Real.sqrt (n : ℝ))⁻¹ := by
    apply (mul_right_cancel₀ hnS.ne')
    rw [mul_assoc, hscalar0, inv_mul_cancel₀ hS.ne', inv_mul_cancel₀ hnS.ne']
  unfold planeDirection planeScale
  rw [hov, latitudeMap, add_sub_cancel_left, smul_smul]
  exact congrArg (fun t : ℝ => t • e x) hscalar

private theorem coarea_constant_slice_factor {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (F G : Vector (n + 1) → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hslice : ∀ a ∈ Ioo (-1 : ℝ) 1,
      (∫⁻ x, F x ∂latitudeLaw u (latitudeFrameAt u) a) =
        C * ∫⁻ x, G x ∂latitudeLaw u (latitudeFrameAt u) a) :
    (∫⁻ x, F x ∂sphereLaw (n + 1)) =
      C * ∫⁻ x, G x ∂sphereLaw (n + 1) := by
  rw [sphereLaw_lintegral_latitudeLaw_at hn u hu F hF,
    sphereLaw_lintegral_latitudeLaw_at hn u hu G hG]
  have hp : (fun r : Ioi (0 : ℝ) => {s : Ioi (0 : ℝ) | (s : ℝ) < 2}.indicator
      (fun s => ENNReal.ofReal ((s : ℝ) *
        (Real.sqrt (1 - (1 - (s : ℝ) ^ 2 / 2) ^ 2)) ^ (n - 2)) *
        ∫⁻ x, F x ∂latitudeLaw u (latitudeFrameAt u) (1 - (s : ℝ) ^ 2 / 2)) r) =
      (fun r : Ioi (0 : ℝ) => C * {s : Ioi (0 : ℝ) | (s : ℝ) < 2}.indicator
        (fun s => ENNReal.ofReal ((s : ℝ) *
          (Real.sqrt (1 - (1 - (s : ℝ) ^ 2 / 2) ^ 2)) ^ (n - 2)) *
          ∫⁻ x, G x ∂latitudeLaw u (latitudeFrameAt u) (1 - (s : ℝ) ^ 2 / 2)) r) := by
    funext r
    by_cases hr : (r : ℝ) < 2
    · rw [indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ) < 2} from hr),
        indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ) < 2} from hr),
        hslice (1 - (r : ℝ) ^ 2 / 2) (radialLatitude_mem ⟨r.property, hr⟩)]
      ac_rfl
    · rw [indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ) < 2} from hr),
        indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ) < 2} from hr), mul_zero]
  rw [hp, lintegral_const_mul' C _ hC]
  ac_rfl

/-- Conditioning the actual sphere on any axial overlap set preserves its
uniform transverse direction. The scalar is the actual restricted mass. -/
theorem restrictedSphere_planeDirection_map {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    ((sphereLaw (n + 1)).restrict (overlapRegion u A)).map (planeDirection u) =
      (sphereLaw (n + 1)) (overlapRegion u A) •
        (sphereLaw n).map (fun x => (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u x) := by
  let d : Vector n → Vector (n + 1) :=
    fun x => (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u x
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hB := overlapRegion_measurable u hA
  ext S hS
  rw [Measure.map_apply (planeDirection_measurable u) hS,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hd hS]
  let C := (sphereLaw n) (d ⁻¹' S)
  have hC : C ≠ ⊤ := measure_ne_top _ _
  let F : Vector (n + 1) → ℝ≥0∞ :=
    (overlapRegion u A).indicator (fun x => S.indicator (fun _ => 1) (planeDirection u x))
  let G : Vector (n + 1) → ℝ≥0∞ := (overlapRegion u A).indicator (fun _ => 1)
  have hF : Measurable F :=
    ((measurable_const.indicator hS).comp (planeDirection_measurable u)).indicator hB
  have hG : Measurable G := measurable_const.indicator hB
  have hs (a : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) :
      (∫⁻ x, F x ∂latitudeLaw u (latitudeFrameAt u) a) =
        C * ∫⁻ x, G x ∂latitudeLaw u (latitudeFrameAt u) a := by
    rw [latitudeLaw, lintegral_map hF (latitudeMap_continuous _ _ _).measurable,
      lintegral_map hG (latitudeMap_continuous _ _ _).measurable]
    have hax (x : Vector n) : overlap (latitudeMap u (latitudeFrameAt u) a x) u = a :=
      overlap_latitude_center u hu _ (latitudeFrameAt_orthogonal u hu) a x
    by_cases haA : a ∈ A
    · have hmem (x : Vector n) : latitudeMap u (latitudeFrameAt u) a x ∈ overlapRegion u A := by
        change overlap _ u ∈ A
        rw [hax]
        exact haA
      simp only [F, G, indicator_of_mem (hmem _),
        planeDirection_latitudeMap (by omega : 1 ≤ n) u hu _
          (latitudeFrameAt_orthogonal u hu) ha]
      have hi : (fun x : Vector n => S.indicator (fun _ => (1 : ℝ≥0∞)) (d x)) =
          (d ⁻¹' S).indicator (fun _ => 1) := by
        rfl
      change (∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) (d x) ∂sphereLaw n) = _
      rw [hi, lintegral_indicator (hS.preimage hd), lintegral_one, lintegral_one]
      simp only [Measure.restrict_apply_univ, measure_univ, mul_one]
      rfl
    · have hnot (x : Vector n) : latitudeMap u (latitudeFrameAt u) a x ∉ overlapRegion u A := by
        change overlap _ u ∉ A
        rw [hax]
        exact haA
      simp only [F, G, indicator_of_notMem (hnot _), lintegral_zero, mul_zero]
  have hh := coarea_constant_slice_factor hn u hu F G hF hG C hC hs
  have hleft : F = ((planeDirection u ⁻¹' S) ∩ overlapRegion u A).indicator (fun _ => 1) := by
    funext x
    by_cases hx : x ∈ overlapRegion u A <;>
      by_cases hy : planeDirection u x ∈ S <;> simp [F, hx, hy]
  rw [hleft, lintegral_indicator ((hS.preimage (planeDirection_measurable u)).inter hB),
    lintegral_one, show G = (overlapRegion u A).indicator (fun _ => 1) from rfl,
    lintegral_indicator hB, lintegral_one, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ] at hh
  rw [Measure.restrict_apply (hS.preimage (planeDirection_measurable u))]
  exact hh.trans (mul_comm _ _)

private theorem restrictedSphere_direction_integral {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A)
    (f : Vector (n + 1) → ℝ) (hf : Measurable f) :
    (∫ σ in overlapRegion u A, f (planeDirection u σ) ∂sphereLaw (n + 1)) =
      (sphereLaw (n + 1)).real (overlapRegion u A) *
        ∫ x, f ((Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u x) ∂sphereLaw n := by
  calc
    _ = ∫ v, f v ∂(((sphereLaw (n + 1)).restrict (overlapRegion u A)).map
        (planeDirection u)) :=
      (integral_map (planeDirection_measurable u).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [restrictedSphere_planeDirection_map hn u hu hA, integral_smul_measure,
        integral_map (by fun_prop : Measurable (fun x : Vector n =>
          (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u x)).aemeasurable
          hf.aestronglyMeasurable]
      rfl

private theorem transverseOffset_direction {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n + 1)) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (x : Vector n) :
    Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q) / q) •
      ((Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u x) =
      transverseOffset (latitudeFrameAt u) q x := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < 1 - q := sub_pos.mpr hq.2
  have hq0 : 0 < q := hq.1
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [transverseOffset, smul_smul]
  congr 1
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnR.le,
    Real.sq_sqrt (by positivity)]
  field_simp

/-- The projected one-factor integral retains its exact quenched pressure,
samplewise, with the actual thick-band mass as the only entropy factor. -/
theorem projectedResidual_logPartition_eq {n : ℕ} (hn : 2 ≤ n)
    (μ : FiniteMixture) (β : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A)
    (hmass : 0 < (sphereLaw (n + 1)).real (overlapRegion u A))
    (J : Disorder (n + 1) μ.maxDegree) :
    Real.log (∫ σ in overlapRegion u A,
      Real.exp (β * taylorRemainderCLM (centerCoefficients (mixtureCoefficients μ) q) u
        (Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q) / q) • planeDirection u σ)
        (euclideanDisorder J)) ∂sphereLaw (n + 1)) / ((n + 1 : ℕ) : ℝ) =
      Real.log ((sphereLaw (n + 1)).real (overlapRegion u A)) / ((n + 1 : ℕ) : ℝ) +
        transverseResidualPressure μ β q u (latitudeFrameAt u) J := by
  let c := centerCoefficients (mixtureCoefficients μ) q
  let H : Vector n → ℝ := fun x =>
    taylorRemainderCLM c u (transverseOffset (latitudeFrameAt u) q x) (euclideanDisorder J)
  have hH : Continuous H := taylorRemainder_parameter_continuous c u _
    (by unfold transverseOffset; fun_prop) _
  have hf : Measurable (fun v : Vector (n + 1) => Real.exp (β *
      taylorRemainderCLM c u
        (Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q) / q) • v) (euclideanDisorder J))) :=
    (Real.continuous_exp.comp ((taylorRemainder_parameter_continuous c u _
      (by fun_prop) _).const_mul β)).measurable
  have hi := restrictedSphere_direction_integral hn u hu hA _ hf
  simp_rw [transverseOffset_direction (by omega : 1 ≤ n) u hq] at hi
  have hZ : 0 < ∫ x, Real.exp (β * H x) ∂sphereLaw n :=
    integral_exp_pos (partition_integrand_integrable (by omega : 1 ≤ n) β hH)
  have hp : transverseResidualPressure μ β q u (latitudeFrameAt u) J =
      Real.log (∫ x, Real.exp (β * H x) ∂sphereLaw n) / ((n + 1 : ℕ) : ℝ) := by
    unfold transverseResidualPressure
    rw [show taylorContinuousField c u
        (fun x : CompactSphereCarrier.Carrier n => transverseOffset (latitudeFrameAt u) q x)
        (transverseOffset_parameter_continuous _ _ Subtype.val continuous_subtype_val)
        (euclideanDisorder J) =
      (⟨fun x => H x, hH.comp continuous_subtype_val⟩ : C(CompactSphereCarrier.Carrier n, ℝ)) from rfl,
      CompactSphereCarrier.logPartition_eq_sphere (by omega : 1 ≤ n) β H hH]
  change Real.log _ / _ = _
  rw [hi, Real.log_mul hmass.ne' hZ.ne', add_div, hp]

private theorem taylorRemainder_center_scale {N P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {q : ℝ} (hq : 0 ≤ q)
    (u z : Vector N) (J : Disorder N P) :
    taylorRemainderCLM (centerCoefficients c q) u z (euclideanDisorder J) =
      taylorRemainderCLM c (Real.sqrt q • u) (Real.sqrt q • z) (euclideanDisorder J) := by
  have hf : field (centerCoefficients c q) J =
      fun x => field c J (Real.sqrt q • x) := funext (field_center_scale c hc hq J)
  have hd : fderiv ℝ (field (centerCoefficients c q) J) u =
      Real.sqrt q • fderiv ℝ (field c J) (Real.sqrt q • u) := by
    rw [hf, fderiv_comp_smul]
  rw [taylorRemainderCLM_actual, taylorRemainderCLM_actual,
    field_center_scale c hc hq, field_center_scale c hc hq, hd, smul_add]
  simp only [smul_apply, map_smul, smul_eq_mul]


/-- The dimension-corrected quenched limit holds at every real inverse
temperature by the actual Gaussian disorder sign symmetry. -/
theorem quenchedPressure_tendsto_dimensionCorrected_per_ambient_all_real
    (μ : FiniteMixture) {β F : ℝ} (j : ℕ)
    (hfixed : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F)) :
    Tendsto (fun N : ℕ => ((N : ℝ) / ((N + j : ℕ) : ℝ)) *
      quenchedPressure N μ (dimensionCorrectedTemperature β j N)) atTop (𝓝 F) := by
  rcases le_total 0 β with hβ | hβ
  · exact quenchedPressure_tendsto_dimensionCorrected_per_ambient μ hβ j hfixed
  · have hf : Tendsto (fun N : ℕ => quenchedPressure N μ (-β)) atTop (𝓝 F) := by
      simpa only [SourceLiteratureParisiTemperatureEven.quenchedPressure_neg] using hfixed
    have ht := quenchedPressure_tendsto_dimensionCorrected_per_ambient μ
      (neg_nonneg.mpr hβ) j hf
    simpa only [dimensionCorrectedTemperature, neg_mul,
      SourceLiteratureParisiTemperatureEven.quenchedPressure_neg] using ht

/-- The literal transverse remainder has the encoded residual limit for
every real temperature, without any Parisi-formula hypothesis. -/
theorem expected_transverseResidualPressure_tendsto_all_real
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => expectedTransverseResidualPressure μ β q
      (latitudeChartPole n) (latitudeChartFrame n)) atTop (𝓝 (D.residual q)) := by
  have ht := quenchedPressure_tendsto_dimensionCorrected_per_ambient_all_real
    (physicalResidualMixture μ q hq) 1 (D.residual_limit q hq)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have he := expected_transverseResidualPressure_eq (by omega : 0 < n + 1) hn
    μ hq β (latitudeChartPole n) (latitudeChartPole_norm_sq n)
    (latitudeChartFrame n) (latitudeChartFrame_orthogonal n)
  simpa only [dimensionCorrectedTemperature] using he.symm

private theorem expected_transverseResidualPressure_eventually_close_all_real
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n + 1), ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ) →
      ∀ e : Vector n →ₗᵢ[ℝ] Vector (n + 1), (∀ y, inner ℝ (e y) u = 0) →
        |expectedTransverseResidualPressure μ β q u e - D.residual q| < ε := by
  have ht := expected_transverseResidualPressure_tendsto_all_real D hq
  have ha : Tendsto (fun n : ℕ => |expectedTransverseResidualPressure μ β q
      (latitudeChartPole n) (latitudeChartFrame n) - D.residual q|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (ht.sub (tendsto_const_nhds (x := D.residual q))).abs
  filter_upwards [ha.eventually (gt_mem_nhds hε), eventually_ge_atTop (1 : ℕ)] with n hn hn0
  intro u hu e he
  have hu' := expected_transverseResidualPressure_eq (by omega : 0 < n + 1) hn0 μ hq β u hu e he
  have hp := expected_transverseResidualPressure_eq (by omega : 0 < n + 1) hn0 μ hq β
    (latitudeChartPole n) (latitudeChartPole_norm_sq n)
    (latitudeChartFrame n) (latitudeChartFrame_orthogonal n)
  rw [hu', ← hp]
  exact hn


open Metric PairConditionalDeterminantMoments
open SphericalAging.GaussianLandscape SphericalAging.GaussianLandscapeMoments
open TwoAtomStationarity SphericalTwoPointCovariance
open scoped NNReal

-- The projection estimates below reproduce the local analytic lemmas of
-- ReplicaBandExpectedUpper, whose declarations are private to that module.
-- The quenched factorization above replaces its final annealed Jensen step.

/-- Actual ambient derivative-norm maximum on the closed physical ball.
The mean value theorem identifies it as a valid ball Lipschitz constant. -/
private def physicalBallLipschitzConstant {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : ℝ :=
  sSup ((fun x => ‖fderiv ℝ (field c J) x‖) '' closedBall 0 (Real.sqrt (N : ℝ)))

attribute [local irreducible] physicalBallLipschitzConstant

private lemma field_fderiv_joint_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (fun z : Disorder N P × Vector N => fderiv ℝ (field c z.1) z.2) :=
  (source_param_fderiv_contDiff (fun J x => field c J x)
    (source_field_joint_contDiff c)).continuous

private lemma physicalBallLipschitzConstant_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (physicalBallLipschitzConstant (N := N) c) := by
  unfold physicalBallLipschitzConstant
  exact (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).continuous_sSup
    (field_fderiv_joint_continuous c).norm

private lemma field_fderiv_ball_image_bddAbove {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) :
    BddAbove ((fun x => ‖fderiv ℝ (field c J) x‖) ''
      closedBall 0 (Real.sqrt (N : ℝ))) := by
  have hc : Continuous (fun x : Vector N => ‖fderiv ℝ (field c J) x‖) :=
    ((field_contDiff c J).fderiv_right (m := ⊤) (by simp)).continuous.norm
  exact ((isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).image hc).bddAbove

private lemma field_fderiv_le_physicalBallLipschitzConstant {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N)
    (hx : x ∈ closedBall 0 (Real.sqrt (N : ℝ))) :
    ‖fderiv ℝ (field c J) x‖ ≤ physicalBallLipschitzConstant c J := by
  unfold physicalBallLipschitzConstant
  exact le_csSup (field_fderiv_ball_image_bddAbove c J) ⟨x,hx,rfl⟩

private lemma physicalBallLipschitzConstant_nonneg {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) :
    0 ≤ physicalBallLipschitzConstant c J := by
  exact (norm_nonneg _).trans (field_fderiv_le_physicalBallLipschitzConstant c J 0
    (by simpa only [mem_closedBall, dist_self] using Real.sqrt_nonneg (N : ℝ)))

/-- No random coefficient bound is assumed in the Lipschitz identification. -/
private theorem physicalBallLipschitzConstant_lipschitzOn {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) :
    LipschitzOnWith ⟨physicalBallLipschitzConstant c J,
      physicalBallLipschitzConstant_nonneg c J⟩
      (field c J) (closedBall 0 (Real.sqrt (N : ℝ))) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (field_contDiff c J).differentiable (by simp) x) _
    (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ)))
  intro x hx
  exact_mod_cast field_fderiv_le_physicalBallLipschitzConstant c J x hx

/-- A genuine integrable random tensor envelope for the physical Lipschitz constant. -/
private def normalizedLipschitzEnvelope {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) *
    landscapeNorm N p.val.val (J p)

private lemma physicalBallLipschitzConstant_le_envelope {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (J : Disorder N P) :
    physicalBallLipschitzConstant c J ≤
      normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ) := by
  unfold physicalBallLipschitzConstant
  apply csSup_le
  · exact ⟨‖fderiv ℝ (field c J) 0‖,0,
      by simpa only [mem_closedBall,dist_self] using Real.sqrt_nonneg (N : ℝ),rfl⟩
  · rintro v ⟨x,hx,rfl⟩
    have hball : ‖x‖ ≤ Real.sqrt (N : ℝ) := by
      simpa only [mem_closedBall,dist_zero_right] using hx
    have hjet := field_iteratedFDeriv_ball_bound hN c J x hball 1
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have hsq : Real.sqrt (N : ℝ)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    simp only [pow_one,norm_iteratedFDeriv_one,Nat.descFactorial_one] at hjet
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ (N : ℝ)*normalizedLipschitzEnvelope c J := hjet
      _ = Real.sqrt (N : ℝ) *
          (normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)) := by
        calc
          _ = normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)^2 := by rw [hsq]; ring
          _ = _ := by ring

private lemma degree_landscapeNorm_integrable_and_mean {N P : ℕ}
    (hN : 1 ≤ N) (p : Degree P) :
    Integrable (fun J : Disorder N P => landscapeNorm N p.val.val (J p))
      (disorderLaw N P) ∧
    (∫ J : Disorder N P, landscapeNorm N p.val.val (J p) ∂disorderLaw N P) ≤
      momentCeiling p.val.val 1 := by
  have hb := uniform_real_power_moment hN (show 0 < p.val.val by omega)
    (k := 1) (by norm_num)
  simp only [Real.rpow_one] at hb
  refine ⟨(degree_block_hasLaw p).integrable_comp hb.1,?_⟩
  have heq := (degree_block_hasLaw (N := N) p).integral_comp hb.1.aestronglyMeasurable
  have heq' : (∫ J : Disorder N P, landscapeNorm N p.val.val (J p) ∂disorderLaw N P) =
      (∫ J : SphericalAging.FiniteModel.Disorder N p.val.val, landscapeNorm N p.val.val J
        ∂SphericalAging.FiniteModel.disorderLaw N p.val.val) := by
    simpa only [Function.comp_def] using heq
  rw [heq']
  exact hb.2

private def lipschitzMeanConstant {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) * momentCeiling p.val.val 1

private lemma normalizedLipschitzEnvelope_integrable {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    Integrable (normalizedLipschitzEnvelope (N := N) c) (disorderLaw N P) := by
  unfold normalizedLipschitzEnvelope
  apply integrable_finsetSum
  intro p hp
  exact (degree_landscapeNorm_integrable_and_mean hN p).1.const_mul _

private lemma expected_normalizedLipschitzEnvelope_le {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    (∫ J : Disorder N P, normalizedLipschitzEnvelope c J ∂disorderLaw N P) ≤
      lipschitzMeanConstant c := by
  unfold normalizedLipschitzEnvelope lipschitzMeanConstant
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (degree_landscapeNorm_integrable_and_mean hN p).2
      (by positivity)
  · intro p hp
    exact (degree_landscapeNorm_integrable_and_mean hN p).1.const_mul _

private lemma physicalBallLipschitzConstant_integrable {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    Integrable (physicalBallLipschitzConstant (N := N) c) (disorderLaw N P) := by
  apply ((normalizedLipschitzEnvelope_integrable hN c).mul_const
    (Real.sqrt (N : ℝ))).mono_nonneg
    (physicalBallLipschitzConstant_continuous c).aestronglyMeasurable
    (ae_of_all _ (physicalBallLipschitzConstant_nonneg c))
    (ae_of_all _ (physicalBallLipschitzConstant_le_envelope hN c))

/-- The actual ball derivative supremum has dimension-free expected scale. -/
private theorem expected_physicalBallLipschitzConstant_le {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    (∫ J : Disorder N P, physicalBallLipschitzConstant c J ∂disorderLaw N P) ≤
      lipschitzMeanConstant c * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∫ J : Disorder N P, normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)
        ∂disorderLaw N P := integral_mono (physicalBallLipschitzConstant_integrable hN c)
      ((normalizedLipschitzEnvelope_integrable hN c).mul_const _)
      (physicalBallLipschitzConstant_le_envelope hN c)
    _ = (∫ J : Disorder N P, normalizedLipschitzEnvelope c J ∂disorderLaw N P) *
        Real.sqrt (N : ℝ) := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (expected_normalizedLipschitzEnvelope_le hN c)
      (Real.sqrt_nonneg _)



/-- Rescaling a center of squared norm `Nq` gives a spherical axis. -/
private theorem normalized_center_norm {N : ℕ} {q : ℝ} (hq : 0 < q)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ) * q) :
    ‖(Real.sqrt q)⁻¹ • m‖ ^ 2 = (N : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hq)), mul_pow, inv_pow,
    Real.sq_sqrt hq.le, hm]
  field_simp

/-- The physical one-replica band lies in a slightly enlarged open cap.
The enlargement is necessary because the band tolerance is non-strict. -/
private theorem band_subset_open_cap {N : ℕ} {q δ : ℝ} (hq : 0 < q)
    (hδ : 0 < δ) (m : Vector N) :
    {σ : Vector N | |overlap σ m - q| ≤ δ * Real.sqrt q} ⊆
      overlapRegion ((Real.sqrt q)⁻¹ • m) (Ioi (Real.sqrt q - 3 * δ / 2)) := by
  intro σ hσ
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  change |overlap σ m - q| ≤ δ * Real.sqrt q at hσ
  have hlo := (abs_le.mp hσ).1
  change Real.sqrt q - 3 * δ / 2 < overlap σ ((Real.sqrt q)⁻¹ • m)
  have he : overlap σ ((Real.sqrt q)⁻¹ • m) = overlap σ m / Real.sqrt q := by
    simp only [overlap, real_inner_smul_right]
    ring
  rw [he]
  apply (lt_div_iff₀ hr).mpr
  nlinarith

/-- The cap prefactor and its dimension correction have vanishing
normalized logarithm, uniformly in the axis. -/
private theorem open_cap_log_bound {N : ℕ} (hN : 3 ≤ N)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hpos : 0 < (sphereLaw N).real (overlapRegion u (Ioi a))) :
    Real.log ((sphereLaw N).real (overlapRegion u (Ioi a))) / (N : ℝ) ≤
      Real.log (1 - a ^ 2) / 2 +
        (Real.log 4 + Real.log (N : ℝ) / 2 - 3 * Real.log (1 - a ^ 2) / 2) /
          (N : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hn : 2 ≤ n := by omega
  have hNr : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hb : 0 < 1 - a ^ 2 := by nlinarith
  have hc := PureCapturePhysicalSphereCapEntropy.sphereLaw_near_one_cap_bound
    hn u hu ha ha1
  have hc' : (sphereLaw (n + 1)).real (overlapRegion u (Ioi a)) ≤
      4 * Real.sqrt ((n + 1 : ℕ) : ℝ) * (Real.sqrt (1 - a ^ 2)) ^ (n - 2) := by
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by push_cast; linarith))
        (by norm_num)) (pow_nonneg (Real.sqrt_nonneg _) _))
  have hl := Real.log_le_log hpos hc'
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hNr.le,
    Real.log_pow, Real.log_sqrt hb.le] at hl
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast] at hl
  apply (div_le_iff₀ hNr).mpr
  calc
    _ ≤ Real.log 4 + Real.log ((n + 1 : ℕ) : ℝ) / 2 +
        ((n : ℝ) - 2) * (Real.log (1 - a ^ 2) / 2) := hl
    _ = _ := by push_cast; field_simp; ring

/-- The thick-band entropy differs from the exact-latitude entropy by
`O(sqrt δ)`, with one constant depending only on the fixed latitude. -/
private theorem band_entropy_eventually_upper {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (hδq : δ ≤ Real.sqrt q / 2)
    (hδ1 : δ ≤ (1 - Real.sqrt q) / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : Vector N,
      ‖m‖ ^ 2 = (N : ℝ) * q →
      0 < (sphereLaw N).real
        {σ : Vector N | |overlap σ m - q| ≤ δ * Real.sqrt q} →
      Real.log ((sphereLaw N).real
        {σ : Vector N | |overlap σ m - q| ≤ δ * Real.sqrt q}) / (N : ℝ) ≤
        Real.log (1 - q) / 2 +
          (3 * Real.sqrt q / (2 * (1 - q))) * Real.sqrt δ + ε := by
  let a : ℝ := Real.sqrt q - 3 * δ / 2
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq.1
  have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.1.le
  have hr1 : Real.sqrt q < 1 := by nlinarith [Real.sqrt_nonneg q]
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hb : 0 < 1 - a ^ 2 := by nlinarith
  have hspos : 0 < 1 - q := by linarith [hq.2]
  have hδle : δ ≤ 1 := by linarith
  have hδsqrt : δ ≤ Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ]
  have hab : 1 - a ^ 2 ≤ 1 - q + 3 * Real.sqrt q * δ := by
    dsimp [a]
    nlinarith [sq_nonneg δ]
  have hlog : Real.log (1 - a ^ 2) / 2 ≤ Real.log (1 - q) / 2 +
      (3 * Real.sqrt q / (2 * (1 - q))) * Real.sqrt δ := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hb hspos)
    rw [Real.log_div hb.ne' hspos.ne'] at ht
    have hdiv : (1 - a ^ 2) / (1 - q) - 1 ≤
        3 * Real.sqrt q * δ / (1 - q) := by
      apply (le_div_iff₀ hspos).mpr
      have he : ((1 - a ^ 2) / (1 - q) - 1) * (1 - q) = q - a ^ 2 := by
        field_simp
        ring
      rw [he]
      linarith
    have ht' := ht.trans hdiv
    have hmul := mul_le_mul_of_nonneg_left hδsqrt
      (show 0 ≤ 3 * Real.sqrt q / (1 - q) by positivity)
    have he : 3 * Real.sqrt q * δ / (1 - q) =
        (3 * Real.sqrt q / (1 - q)) * δ := by ring
    rw [he] at ht'
    have he' : (3 * Real.sqrt q / (2 * (1 - q))) * Real.sqrt δ =
        (3 * Real.sqrt q / (1 - q)) * Real.sqrt δ / 2 := by
      field_simp
    rw [he']
    linarith
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun N : ℕ =>
      (Real.log 4 + Real.log (N : ℝ) / 2 - 3 * Real.log (1 - a ^ 2) / 2) /
        (N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log 4 - 3 * Real.log (1 - a ^ 2) / 2)).add (hlogN.div_const 2)
    convert hh using 1
    · ext N
      ring
    · norm_num
  filter_upwards [eventually_ge_atTop 3, herr.eventually (gt_mem_nhds hε)]
    with N hN heps
  intro m hm hpos
  let u : Vector N := (Real.sqrt q)⁻¹ • m
  have hu : ‖u‖ ^ 2 = (N : ℝ) := normalized_center_norm hq.1 m hm
  have hsub : {σ : Vector N | |overlap σ m - q| ≤ δ * Real.sqrt q} ⊆
      overlapRegion u (Ioi a) := band_subset_open_cap hq.1 hδ m
  have hmass := measureReal_mono (μ := sphereLaw N) hsub
  have hcap : 0 < (sphereLaw N).real (overlapRegion u (Ioi a)) :=
    hpos.trans_le hmass
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hband := div_le_div_of_nonneg_right (Real.log_le_log hpos hmass) hNpos.le
  have hbound := open_cap_log_bound hN u hu ha ha1 hcap
  exact hband.trans (hbound.trans (by linarith))



/-- Physical, uncentered coefficient-space variance at the exact latitude. -/
private theorem physical_taylorRemainder_coupling {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q : ℝ} (m v : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q)
    (hv : ‖v‖ ^ 2 = (N : ℝ) * (1 - q)) (ht : inner ℝ v m = 0) :
    taylorRemainderCLM (mixtureCoefficients μ) m v
      ((taylorRemainderCLM (mixtureCoefficients μ) m v).adjoint 1) =
        (N : ℝ) * residualAtOne μ q := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hmm : overlap m m = q := by
    unfold overlap
    rw [real_inner_self_eq_norm_sq, hm]
    field_simp [hN0]
  have hvv : overlap v v = 1 - q := by
    unfold overlap
    rw [real_inner_self_eq_norm_sq, hv]
    field_simp [hN0]
  rw [taylorRemainder_coupling hN _ (mixtureCoefficients_nonnegative μ) m v v ht ht,
    hmm, hvv, show q + (1 - q) = 1 by ring,
    covariancePolynomial_mixture, covariancePolynomial_mixture,
    firstCovariance_mixture, real_inner_self_eq_norm_sq, hv]
  unfold residualAtOne
  ring

/-- The squared scalar coefficient norm is its self coupling. -/
private theorem scalar_norm_sq_eq_coupling {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] ℝ) :
    ‖A‖ ^ 2 = A (A.adjoint 1) := by
  have hA : A = innerSL ℝ (A.adjoint 1) := by
    ext g
    rw [innerSL_apply_apply, A.adjoint_inner_left]
    simp
  have hnorm : ‖A‖ = ‖A.adjoint 1‖ := by
    calc
      ‖A‖ = ‖innerSL ℝ (A.adjoint 1)‖ := congrArg norm hA
      _ = ‖A.adjoint 1‖ := innerSL_apply_norm ℝ _
  calc
    ‖A‖ ^ 2 = ‖A.adjoint 1‖ ^ 2 := congrArg (fun r : ℝ => r ^ 2) hnorm
    _ = A (A.adjoint 1) := by
      rw [← real_inner_self_eq_norm_sq, A.adjoint_inner_left]
      simp

/-- Uniform scalar coefficient norm on the physical exact latitude. -/
private theorem physical_taylorRemainder_norm {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q : ℝ} (m v : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q)
    (hv : ‖v‖ ^ 2 = (N : ℝ) * (1 - q)) (ht : inner ℝ v m = 0) :
    ‖taylorRemainderCLM (mixtureCoefficients μ) m v‖ =
      Real.sqrt ((N : ℝ) * residualAtOne μ q) := by
  rw [← physical_taylorRemainder_coupling hN μ m v hm hv ht,
    ← scalar_norm_sq_eq_coupling, Real.sqrt_sq (norm_nonneg _)]

/-- The projected Taylor coefficient itself is a Borel continuous-linear-map
valued function; a finite coordinate expansion reduces this to scalar evaluations. -/
private theorem projected_taylorRemainderCLM_measurable {N P : ℕ} (c : Degree P → ℝ)
    (m : Vector N) (v : Vector N → Vector N) (hv : Measurable v) :
    Measurable (fun σ => taylorRemainderCLM c m (v σ)) := by
  classical
  let b := EuclideanSpace.basisFun (Coordinate N P) ℝ
  have heq : (fun σ => taylorRemainderCLM c m (v σ)) =
      fun σ => ∑ i : Coordinate N P,
        taylorRemainderCLM c m (v σ) (b i) • EuclideanSpace.proj i := by
    funext σ
    ext g
    simp only [sum_apply, smul_apply,
      smul_eq_mul, EuclideanSpace.coe_proj]
    calc
      taylorRemainderCLM c m (v σ) g =
          taylorRemainderCLM c m (v σ) (∑ i, g i • b i) := by
        congr 1
        exact (b.sum_repr g).symm
      _ = _ := by simp [map_sum, map_smul, mul_comm]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  have hi : Measurable (fun σ => taylorRemainderCLM c m (v σ) (b i)) := by
    have hc : Continuous (fun z : Vector N => taylorRemainderCLM c m z (b i)) :=
      taylorRemainder_parameter_continuous c m id continuous_id (b i)
    exact hc.measurable.comp hv
  exact hi.smul_const _

/-- The upper semicircle is one-half Hölder in its axial coordinate, with
its exact constant needed for the band projection. -/
private theorem semicircle_chord_sq_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (a-b)^2 + (Real.sqrt (1-a^2)-Real.sqrt (1-b^2))^2 ≤ 2*|a-b| := by
  have ordered (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
      (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a ≤ b) :
      (a-b)^2 + (Real.sqrt (1-a^2)-Real.sqrt (1-b^2))^2 ≤ 2*(b-a) := by
    have ha2 : 0 ≤ 1-a^2 := by nlinarith
    have hb2 : 0 ≤ 1-b^2 := by nlinarith
    have hx := Real.sq_sqrt ha2
    have hy := Real.sq_sqrt hb2
    have hp : 0 ≤ 2*(1-b)*(1+a)*(b-a) := by positivity
    have he : (1-a^2)*(1-b^2)-((1-b)*(1+a))^2 =
        2*(1-b)*(1+a)*(b-a) := by ring
    have hsq : ((1-b)*(1+a))^2 ≤
        (Real.sqrt (1-a^2)*Real.sqrt (1-b^2))^2 := by
      simp only [mul_pow,hx,hy]
      nlinarith
    have hl : (1-b)*(1+a) ≤ Real.sqrt (1-a^2)*Real.sqrt (1-b^2) :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    nlinarith
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using ordered a b ha0 ha1 hb0 hb1 hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have h := ordered b a hb0 hb1 ha0 ha1 hba
    nlinarith [h]

/-- Unit directions with pairwise Gram entries at most `r` have a controlled
replica sum. This is the deterministic linear-term gain in the manuscript. -/
private theorem unitDirections_sum_norm_sq_le {N k : ℕ} (ω : Fin k → Vector N)
    (hω : ∀ i, ‖ω i‖ = 1) {r : ℝ}
    (hpair : ∀ i j, i ≠ j → inner ℝ (ω i) (ω j) ≤ r) :
    ‖∑ i, ω i‖^2 ≤ (k : ℝ)+(k : ℝ)*((k : ℝ)-1)*r := by
  classical
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  simp_rw [inner_sum]
  calc
    ∑ i : Fin k, ∑ j : Fin k, inner ℝ (ω i) (ω j) ≤
        ∑ i : Fin k, (1+((k : ℝ)-1)*r) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        real_inner_self_eq_norm_sq,hω i]
      norm_num only [one_pow]
      apply add_le_add_right
      calc
        ∑ j ∈ Finset.univ.erase i, inner ℝ (ω i) (ω j) ≤
            ∑ _j ∈ Finset.univ.erase i, r := by
          apply Finset.sum_le_sum
          intro j hj
          exact hpair i j (Ne.symm (Finset.ne_of_mem_erase hj))
        _ = ((k : ℝ)-1)*r := by
          rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i)]
          have hk : 1 ≤ k := by have hi := i.isLt; omega
          simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          rw [Nat.cast_sub hk,Nat.cast_one]
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- The convenient square-root form of the replica Gram bound. -/
private theorem unitDirections_sum_norm_le {N k : ℕ} (hk : 1 ≤ k)
    (ω : Fin k → Vector N) (hω : ∀ i, ‖ω i‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hpair : ∀ i j, i ≠ j → inner ℝ (ω i) (ω j) ≤ r) :
    ‖∑ i, ω i‖ ≤ (k : ℝ)*Real.sqrt (1/(k : ℝ)+r) := by
  have hk0 : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs := Real.sq_sqrt (show 0 ≤ 1/(k : ℝ)+r by positivity)
  have hb := unitDirections_sum_norm_sq_le ω hω hpair
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,hs]
  have he : (k : ℝ)^2*(1/(k : ℝ)+r)=(k : ℝ)+(k : ℝ)^2*r := by
    field_simp
  rw [he]
  nlinarith

/-- Changing both points on the physical sphere changes their overlap by
at most the sum of their chord errors divided by the sphere radius. -/
private theorem overlap_perturbation_le {N : ℕ} (hN : 0 < N)
    (x y x' y' : Vector N) (hx : ‖x‖^2=(N : ℝ)) (hy' : ‖y'‖^2=(N : ℝ)) :
    |overlap x' y'-overlap x y| ≤
      (‖x'-x‖+‖y'-y‖)/Real.sqrt (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hss := Real.sq_sqrt hNr.le
  have hxn : ‖x‖=Real.sqrt (N : ℝ) :=
    (sq_eq_sq₀ (norm_nonneg _) hs.le).mp (hx.trans hss.symm)
  have hyn : ‖y'‖=Real.sqrt (N : ℝ) :=
    (sq_eq_sq₀ (norm_nonneg _) hs.le).mp (hy'.trans hss.symm)
  have he : inner ℝ x' y'-inner ℝ x y =
      inner ℝ (x'-x) y'+inner ℝ x (y'-y) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  unfold overlap
  rw [← sub_div,abs_div,abs_of_pos hNr,he]
  calc
    _ ≤ (‖x'-x‖*Real.sqrt (N : ℝ)+Real.sqrt (N : ℝ)*‖y'-y‖)/(N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNr.le
      exact (abs_add_le _ _).trans (add_le_add
        (by simpa only [hyn] using abs_real_inner_le_norm (x'-x) y')
        (by simpa only [hxn] using abs_real_inner_le_norm x (y'-y)))
    _ = _ := by field_simp; rw [hss]; ring

/-- The sphere point above a normalized transverse direction has exact
latitude `q` and exact physical radius. -/
private theorem exactLatitude_norm_sq {N : ℕ} (m ω : Vector N) {q : ℝ}
    (hq : q ≤ 1) (hm : ‖m‖^2=(N : ℝ)*q) (hω : ‖ω‖=1)
    (horth : inner ℝ ω m=0) :
    ‖m+Real.sqrt ((N : ℝ)*(1-q)) • ω‖^2=(N : ℝ) := by
  have horth' : inner ℝ m ω=0 := by rw [real_inner_comm]; exact horth
  rw [norm_add_sq_real,hm,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hω,one_pow,mul_one,
    Real.sq_sqrt (by positivity),real_inner_smul_right,horth']
  ring

/-- The physical center rescaled to the original sphere. -/
private def bandReference {N : ℕ} (q : ℝ) (m : Vector N) : Vector N :=
  (Real.sqrt q)⁻¹ • m

/-- The normalized transverse direction, defined everywhere so its
restriction to the positive-width band is measurable. -/
private def bandDirection {N : ℕ} (q : ℝ) (m σ : Vector N) : Vector N :=
  planeDirection (bandReference q m) σ

/-- Projection of the thick band to its exact central latitude. -/
private def bandProjection {N : ℕ} (q : ℝ) (m σ : Vector N) : Vector N :=
  m+Real.sqrt ((N : ℝ)*(1-q)) • bandDirection q m σ

/-- Normalization of the center has the exact original-sphere radius. -/
private theorem bandReference_norm_sq {N : ℕ} (q : ℝ) (m : Vector N)
    (hq : 0 < q) (hm : ‖m‖^2=(N : ℝ)*q) :
    ‖bandReference q m‖^2=(N : ℝ) := by
  rw [bandReference,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,hm,
    Real.sq_sqrt hq.le]
  field_simp [hq.ne']

private theorem bandReference_center {N : ℕ} (q : ℝ) (m : Vector N) (hq : 0 < q) :
    Real.sqrt q • bandReference q m=m := by
  rw [bandReference,smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hq).ne',one_smul]

/-- The band tolerance is exactly the axial-coordinate tolerance after
center normalization. -/
private theorem bandReference_overlap_tolerance {N : ℕ} (q δ : ℝ) (m σ : Vector N)
    (hq : 0 < q) (hband : |overlap σ m-q| ≤ δ*Real.sqrt q) :
    |overlap (bandReference q m) σ-Real.sqrt q| ≤ δ := by
  have hr := Real.sqrt_pos.mpr hq
  have he : overlap (bandReference q m) σ-Real.sqrt q =
      (overlap σ m-q)/Real.sqrt q := by
    have hscale : overlap (bandReference q m) σ=(Real.sqrt q)⁻¹*overlap σ m := by
      rw [bandReference,overlap,real_inner_smul_left,overlap,real_inner_comm m σ]
      ring
    rw [hscale]
    have hs := Real.sq_sqrt hq.le
    field_simp [hr.ne']
    nlinarith
  rw [he,abs_div,abs_of_pos hr]
  exact (div_le_iff₀ hr).mpr hband

/-- The permitted band is strictly in the upper open hemisphere and stays
away from the pole; hence its transverse normalization is nonzero. -/
private theorem bandReference_overlap_range {N : ℕ} {q δ : ℝ} (m σ : Vector N)
    (hq : q∈Ioo (0 : ℝ) 1) (hδ0 : 0 ≤ δ)
    (hδq : δ ≤ Real.sqrt q/2) (hδ1 : δ ≤ (1-Real.sqrt q)/2)
    (hband : |overlap σ m-q| ≤ δ*Real.sqrt q) :
    overlap (bandReference q m) σ∈Ioo (0 : ℝ) 1 := by
  have hr0 := Real.sqrt_pos.mpr hq.1
  have hr1 : Real.sqrt q < 1 := by
    have hs := Real.sq_sqrt hq.1.le
    nlinarith [Real.sqrt_nonneg q,hq.2]
  have htol := abs_le.mp (bandReference_overlap_tolerance q δ m σ hq.1 hband)
  constructor <;> linarith

/-- Actual projected directions are unit and orthogonal to the physical
center, uniformly over every sphere point in the thick band. -/
private theorem bandDirection_geometry {N : ℕ} (hN : 0 < N) {q δ : ℝ}
    (m σ : Vector N) (hq : q∈Ioo (0 : ℝ) 1)
    (hm : ‖m‖^2=(N : ℝ)*q) (hσ : ‖σ‖^2=(N : ℝ))
    (hδ0 : 0 ≤ δ) (hδq : δ ≤ Real.sqrt q/2)
    (hδ1 : δ ≤ (1-Real.sqrt q)/2)
    (hband : |overlap σ m-q| ≤ δ*Real.sqrt q) :
    ‖bandDirection q m σ‖=1 ∧ inner ℝ (bandDirection q m σ) m=0 := by
  have hu := bandReference_norm_sq q m hq.1 hm
  have hr := bandReference_overlap_range m σ hq hδ0 hδq hδ1 hband
  have habs : |overlap (bandReference q m) σ| < 1 := by
    rw [abs_of_pos hr.1]
    exact hr.2
  constructor
  · exact planeDirection_norm hN _ _ hu hσ habs
  · calc
      inner ℝ (bandDirection q m σ) m =
          inner ℝ (bandDirection q m σ) (Real.sqrt q • bandReference q m) := by
        rw [bandReference_center q m hq.1]
      _ = 0 := by
        rw [real_inner_smul_right,bandDirection,planeDirection_tangent hN _ _ hu,mul_zero]

/-- The actual thick-band projection has exact sphere radius. -/
private theorem bandProjection_norm_sq {N : ℕ} (hN : 0 < N) {q δ : ℝ}
    (m σ : Vector N) (hq : q∈Ioo (0 : ℝ) 1)
    (hm : ‖m‖^2=(N : ℝ)*q) (hσ : ‖σ‖^2=(N : ℝ))
    (hδ0 : 0 ≤ δ) (hδq : δ ≤ Real.sqrt q/2)
    (hδ1 : δ ≤ (1-Real.sqrt q)/2)
    (hband : |overlap σ m-q| ≤ δ*Real.sqrt q) :
    ‖bandProjection q m σ‖^2=(N : ℝ) := by
  have hg := bandDirection_geometry hN m σ hq hm hσ hδ0 hδq hδ1 hband
  exact exactLatitude_norm_sq m _ hq.2.le hm hg.1 hg.2

/-- The measurable normalization used in the projected one-factor integral. -/
private theorem bandDirection_measurable {N : ℕ} (q : ℝ) (m : Vector N) :
    Measurable (bandDirection q m) := by
  unfold bandDirection planeDirection planeScale overlap
  fun_prop

/-- Projection to the exact latitude costs at most `√(2Nδ)` in physical
chord distance. -/
private theorem bandProjection_dist_le {N : ℕ} (hN : 0 < N) {q δ : ℝ}
    (m σ : Vector N) (hq : q∈Ioo (0 : ℝ) 1)
    (hm : ‖m‖^2=(N : ℝ)*q) (hσ : ‖σ‖^2=(N : ℝ))
    (hδ0 : 0 ≤ δ) (hδq : δ ≤ Real.sqrt q/2)
    (hδ1 : δ ≤ (1-Real.sqrt q)/2)
    (hband : |overlap σ m-q| ≤ δ*Real.sqrt q) :
    ‖σ-bandProjection q m σ‖ ≤ Real.sqrt (2*(N : ℝ)*δ) := by
  let u := bandReference q m
  let a := overlap u σ
  let r := Real.sqrt q
  let ω := bandDirection q m σ
  have hu : ‖u‖^2=(N : ℝ) := bandReference_norm_sq q m hq.1 hm
  have ha : a∈Ioo (0 : ℝ) 1 := bandReference_overlap_range m σ hq hδ0 hδq hδ1 hband
  have hr0 : 0 < r := Real.sqrt_pos.mpr hq.1
  have hr2 : r^2=q := Real.sq_sqrt hq.1.le
  have hr1 : r < 1 := by nlinarith [hq.2]
  have habs : |overlap u σ| < 1 := by rw [abs_of_pos ha.1]; exact ha.2
  have hscale := planeScale_pos hN u σ habs
  have hω : ‖ω‖=1 := (bandDirection_geometry hN m σ hq hm hσ hδ0 hδq hδ1 hband).1
  have horth : inner ℝ u ω=0 := by
    rw [real_inner_comm]
    exact planeDirection_tangent hN u σ hu
  have hdecomp : σ=a • u+planeScale u σ • ω := by
    dsimp only [ω,bandDirection]
    change σ=a • u+planeScale u σ • planeDirection u σ
    rw [planeDirection,smul_smul,mul_inv_cancel₀ hscale.ne',one_smul]
    dsimp only [a]
    module
  have hmdecomp : m=r • u := (bandReference_center q m hq.1).symm
  have he : σ-bandProjection q m σ=
      (a-r) • u+(planeScale u σ-Real.sqrt ((N : ℝ)*(1-q))) • ω := by
    change σ-(m+Real.sqrt ((N : ℝ)*(1-q)) • ω)=_
    nth_rw 1 [hdecomp]
    nth_rw 1 [hmdecomp]
    module
  have hnorm : ‖σ-bandProjection q m σ‖^2 =
      (N : ℝ)*((a-r)^2+(Real.sqrt (1-a^2)-Real.sqrt (1-r^2))^2) := by
    rw [he,norm_add_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      mul_pow,mul_pow,sq_abs,sq_abs,hu,hω,one_pow,mul_one,
      real_inner_smul_left,real_inner_smul_right,horth]
    have ha2 : 0 ≤ 1-a^2 := by nlinarith [ha.1,ha.2]
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    have hscaleeq : planeScale u σ=Real.sqrt (N : ℝ)*Real.sqrt (1-a^2) := by
      exact Real.sqrt_mul hN0 _
    have hrad : Real.sqrt ((N : ℝ)*(1-q))=
        Real.sqrt (N : ℝ)*Real.sqrt (1-r^2) := by
      rw [hr2]
      exact Real.sqrt_mul hN0 _
    rw [hscaleeq,hrad]
    have hs := Real.sq_sqrt hN0
    simp only [mul_zero,add_zero]
    rw [← mul_sub,mul_pow,hs]
    ring
  have hchord := semicircle_chord_sq_le ha.1.le ha.2.le hr0.le hr1.le
  have htol : |a-r| ≤ δ := bandReference_overlap_tolerance q δ m σ hq.1 hband
  have hbound : ‖σ-bandProjection q m σ‖^2 ≤ 2*(N : ℝ)*δ := by
    rw [hnorm]
    have h := mul_le_mul_of_nonneg_left hchord (show 0 ≤ (N : ℝ) by positivity)
    have h' := mul_le_mul_of_nonneg_left htol (show 0 ≤ 2*(N : ℝ) by positivity)
    nlinarith
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hbound

/-- On an exact latitude, the projected overlap consists of the common
center contribution and the transverse Gram entry. -/
private theorem exactLatitude_pair_overlap {N : ℕ} (hN : 0 < N)
    (m ω η : Vector N) {q : ℝ} (hq : q ≤ 1)
    (hm : ‖m‖^2=(N : ℝ)*q) (hω : inner ℝ ω m=0) (hη : inner ℝ η m=0) :
    overlap (m+Real.sqrt ((N : ℝ)*(1-q)) • ω)
      (m+Real.sqrt ((N : ℝ)*(1-q)) • η)=q+(1-q)*inner ℝ ω η := by
  have hη' : inner ℝ m η=0 := by rw [real_inner_comm]; exact hη
  have hs := Real.sq_sqrt (show 0 ≤ (N : ℝ)*(1-q) by positivity)
  have he : inner ℝ (m+Real.sqrt ((N : ℝ)*(1-q)) • ω)
      (m+Real.sqrt ((N : ℝ)*(1-q)) • η)=
      (N : ℝ)*q+(Real.sqrt ((N : ℝ)*(1-q)))^2*inner ℝ ω η := by
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,hω,hη',real_inner_self_eq_norm_sq,hm]
    ring
  unfold overlap
  rw [he,hs]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

/-- Chord errors of `√(2Nδ)` at both endpoints give exactly `√(8δ)`
for the physical overlap. -/
private theorem overlap_perturbation_sqrt_le {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ)
    (x y x' y' : Vector N) (hx : ‖x‖^2=(N : ℝ)) (hy' : ‖y'‖^2=(N : ℝ))
    (hxx' : ‖x'-x‖ ≤ Real.sqrt (2*(N : ℝ)*δ))
    (hyy' : ‖y'-y‖ ≤ Real.sqrt (2*(N : ℝ)*δ)) :
    |overlap x' y'-overlap x y| ≤ Real.sqrt (8*δ) := by
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hsqrt : Real.sqrt (2*(N : ℝ)*δ)=Real.sqrt (N : ℝ)*Real.sqrt (2*δ) := by
    rw [show 2*(N : ℝ)*δ=(N : ℝ)*(2*δ) by ring]
    exact Real.sqrt_mul (by positivity) _
  have hdouble : 2*Real.sqrt (2*δ)=Real.sqrt (8*δ) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    ring
  calc
    _ ≤ (‖x'-x‖+‖y'-y‖)/Real.sqrt (N : ℝ) :=
      overlap_perturbation_le hN x y x' y' hx hy'
    _ ≤ (Real.sqrt (2*(N : ℝ)*δ)+Real.sqrt (2*(N : ℝ)*δ))/Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_right (add_le_add hxx' hyy') hsN.le
    _ = 2*Real.sqrt (2*δ) := by rw [hsqrt]; field_simp; ring
    _ = _ := hdouble

/-- Replica pairs in the original thick band become nearly orthogonal
unit transverse directions on the exact central latitude. -/
private theorem bandDirection_pair_bound {N : ℕ} (hN : 0 < N) {q δ ρ : ℝ}
    (m σ τ : Vector N) (hq : q∈Ioo (0 : ℝ) 1)
    (hm : ‖m‖^2=(N : ℝ)*q) (hσ : ‖σ‖^2=(N : ℝ)) (hτ : ‖τ‖^2=(N : ℝ))
    (hδ0 : 0 ≤ δ) (hδq : δ ≤ Real.sqrt q/2) (hδ1 : δ ≤ (1-Real.sqrt q)/2)
    (hσband : |overlap σ m-q| ≤ δ*Real.sqrt q)
    (hτband : |overlap τ m-q| ≤ δ*Real.sqrt q)
    (hpair : |overlap σ τ-q| < ρ) :
    |inner ℝ (bandDirection q m σ) (bandDirection q m τ)| <
      (ρ+Real.sqrt (8*δ))/(1-q) := by
  have hgσ := bandDirection_geometry hN m σ hq hm hσ hδ0 hδq hδ1 hσband
  have hgτ := bandDirection_geometry hN m τ hq hm hτ hδ0 hδq hδ1 hτband
  have hdσ := bandProjection_dist_le hN m σ hq hm hσ hδ0 hδq hδ1 hσband
  have hdτ := bandProjection_dist_le hN m τ hq hm hτ hδ0 hδq hδ1 hτband
  have hnτ := bandProjection_norm_sq hN m τ hq hm hτ hδ0 hδq hδ1 hτband
  have herror := overlap_perturbation_sqrt_le hN hδ0 σ τ
    (bandProjection q m σ) (bandProjection q m τ) hσ hnτ
    (by simpa only [norm_sub_rev] using hdσ) (by simpa only [norm_sub_rev] using hdτ)
  have hs : 0 < 1-q := sub_pos.mpr hq.2
  have he : overlap (bandProjection q m σ) (bandProjection q m τ)-q =
      (1-q)*inner ℝ (bandDirection q m σ) (bandDirection q m τ) := by
    rw [bandProjection,bandProjection,exactLatitude_pair_overlap hN m _ _ hq.2.le hm hgσ.2 hgτ.2]
    ring
  have hb : |overlap (bandProjection q m σ) (bandProjection q m τ)-q| <
      ρ+Real.sqrt (8*δ) := by
    calc
      _ = |(overlap (bandProjection q m σ) (bandProjection q m τ)-overlap σ τ)+
          (overlap σ τ-q)| := by congr 1; ring
      _ ≤ |overlap (bandProjection q m σ) (bandProjection q m τ)-overlap σ τ|+
          |overlap σ τ-q| := abs_add_le _ _
      _ < Real.sqrt (8*δ)+ρ := add_lt_add_of_le_of_lt herror hpair
      _ = _ := by ring
  rw [he,abs_mul,abs_of_pos hs] at hb
  exact (lt_div_iff₀ hs).mpr (by simpa only [mul_comm] using hb)


private theorem finite_logPartition_bound {V H : Type*} [MeasurableSpace V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    |GaussianSpinInterpolation.logPartition ν L w| ≤
      |Real.log (ν.real univ)| + K * ‖w‖ := by
  have hi := GaussianSpinInterpolation.weight_integrable ν (fun _ => 1) L
    measurable_const hL
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  have hmass := measureReal_univ_pos (μ := ν)
  have hz := GaussianSpinInterpolation.moment_one_pos ν L hL hb w
  have hlo : ν.real univ * Real.exp (-K * ‖w‖) ≤
      GaussianSpinInterpolation.moment ν (fun _ => 1) L w := by
    have h := integral_mono_ae (integrable_const (Real.exp (-K * ‖w‖))) hi
      (hb.mono (fun v hv => by
        simp only [GaussianSpinInterpolation.weight, one_mul]
        apply Real.exp_le_exp.mpr
        have hh := (L v).le_opNorm w |>.trans
          (mul_le_mul_of_nonneg_right hv (norm_nonneg w))
        rw [Real.norm_eq_abs] at hh
        linarith [neg_le_abs (L v w)]))
    simpa only [integral_const, smul_eq_mul, GaussianSpinInterpolation.moment] using h
  have hhi : GaussianSpinInterpolation.moment ν (fun _ => 1) L w ≤
      ν.real univ * Real.exp (K * ‖w‖) := by
    have h := integral_mono_ae hi (integrable_const (Real.exp (K * ‖w‖)))
      (hb.mono (fun v hv => by
        simp only [GaussianSpinInterpolation.weight, one_mul]
        apply Real.exp_le_exp.mpr
        have hh := (L v).le_opNorm w |>.trans
          (mul_le_mul_of_nonneg_right hv (norm_nonneg w))
        exact (le_abs_self _).trans hh))
    simpa only [integral_const, smul_eq_mul, GaussianSpinInterpolation.moment] using h
  have hl := Real.log_le_log (mul_pos hmass (Real.exp_pos _)) hlo
  have hu := Real.log_le_log hz hhi
  rw [Real.log_mul hmass.ne' (Real.exp_ne_zero _), Real.log_exp] at hl hu
  change Real.log (ν.real univ) + -K * ‖w‖ ≤
    GaussianSpinInterpolation.logPartition ν L w at hl
  change GaussianSpinInterpolation.logPartition ν L w ≤
    Real.log (ν.real univ) + K * ‖w‖ at hu
  exact abs_le.mpr ⟨by linarith [neg_le_abs (Real.log (ν.real univ))],
    by linarith [le_abs_self (Real.log (ν.real univ))]⟩

private theorem finite_logPartition_gaussian_integrable {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    Integrable (GaussianSpinInterpolation.logPartition ν L)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc := (GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).continuous
  apply ((integrable_const |Real.log (ν.real univ)|).add
    (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K)).mono'
    hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs]
    exact finite_logPartition_bound ν L hL hb w

/-- Both the closed center tolerance and strict pair tolerance are measurable. -/
private theorem replicatedBand_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

/-- A positive replicated band gives positive mass to its one-replica band. -/
private theorem oneBand_real_pos_of_replicatedBand_pos {N k : ℕ} (hk : 1 ≤ k)
    (q δ ρ : ℝ) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) :
    0 < (sphereLaw N).real
      {σ : Vector N | |overlap σ m - q| ≤ δ * Real.sqrt q} := by
  let B : Set (Vector N) := {σ | |overlap σ m - q| ≤ δ * Real.sqrt q}
  have hsub : ReplicatedBand k q δ ρ m ⊆ univ.pi (fun _ : Fin k => B) := by
    intro σ hσ i _
    exact hσ.1 i
  have hp : 0 < (sphereLaw N B) ^ k := by
    have hh := hvol.trans_le (measure_mono hsub)
    simpa only [Measure.pi_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hh
  have hn : sphereLaw N B ≠ 0 := by
    intro hz
    simp only [hz, zero_pow (by omega : k ≠ 0), lt_self_iff_false] at hp
  exact ENNReal.toReal_pos hn (measure_ne_top _ _)

/-- The finite replicated exponential is spatially integrable, before
restricting to the band. -/
private theorem replicatedBand_integrand_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    Integrable (fun σ : Fin k → Vector N =>
      Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (σ i) -
          field (mixtureCoefficients μ) J m)))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) := by
  have hi : Integrable (fun x : Vector N =>
      Real.exp (β * (field (mixtureCoefficients μ) J x -
        field (mixtureCoefficients μ) J m))) (sphereLaw N) :=
    partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β
      ((field_contDiff _ J).continuous.sub continuous_const)
  have hp := Integrable.fintype_prod (fun _ : Fin k => hi)
  convert hp using 1
  ext σ
  rw [Finset.mul_sum, Real.exp_sum]

/-- Positive surface volume makes the replicated partition strictly positive
for every disorder realization. -/
private theorem replicatedBandPartition_pos {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) :
    0 < replicatedBandPartition k μ β q δ ρ J m := by
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) := ⟨hvol.ne'⟩
  exact integral_exp_pos
    (replicatedBand_integrand_integrable hN μ β J m).restrict

/-- The physical replicated-band pressure is integrable under the literal
disorder law whenever its deterministic surface volume is positive. -/
private theorem replicatedBandPressure_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) :
    Integrable (fun J : Disorder N μ.maxDegree =>
      replicatedBandPressure k μ β q δ ρ J m) (disorderLaw N μ.maxDegree) := by
  let ν := (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict
    (ReplicatedBand k q δ ρ m)
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) := ⟨hvol.ne'⟩
  have : NeZero ν := inferInstance
  let L : (Fin k → Vector N) → EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
    fun σ => β • ∑ i : Fin k,
      (sphereLinear (mixtureCoefficients μ) (σ i) - sphereLinear (mixtureCoefficients μ) m)
  let K : ℝ := |β| * (k : ℝ) *
    (Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) +
      ‖sphereLinear (mixtureCoefficients μ) m‖)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : Measurable L := by
    have hs : Measurable (fun σ : Fin k → Vector N => ∑ i : Fin k,
        (sphereLinear (mixtureCoefficients μ) (σ i) -
          sphereLinear (mixtureCoefficients μ) m)) := by
      apply Finset.measurable_sum
      intro i _
      exact ((sphereLinear_measurable _).comp (measurable_pi_apply i)).sub measurable_const
    exact (measurable_const : Measurable (fun _ : Fin k → Vector N => β)).smul hs
  have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N), ∀ i : Fin k,
      ‖sphereLinear (mixtureCoefficients μ) (σ i)‖ ≤
        Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) :=
    eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin k => sphereLaw N) (i := i)).eventually
        (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ)))
  have hb : ∀ᵐ σ ∂ν, ‖L σ‖ ≤ K := by
    filter_upwards [ha.filter_mono ae_restrict_le] with σ hσ
    dsimp [L, K]
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
    calc
      _ ≤ ∑ i : Fin k,
          ‖sphereLinear (mixtureCoefficients μ) (σ i) -
            sphereLinear (mixtureCoefficients μ) m‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k,
          (Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) +
            ‖sphereLinear (mixtureCoefficients μ) m‖) := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_sub_le _ _).trans (add_le_add (hσ i) (le_refl _))
      _ = _ := by simp; ring
  have hi := finite_logPartition_gaussian_integrable ν L hL hK hb
  have hic := (euclideanDisorder_hasLaw N μ.maxDegree).integrable_comp hi
  have he (J : Disorder N μ.maxDegree) :
      GaussianSpinInterpolation.logPartition ν L (euclideanDisorder J) =
        Real.log (replicatedBandPartition k μ β q δ ρ J m) := by
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    congr 1
    apply integral_congr_ae
    exact .of_forall fun σ => by
      simp only [GaussianSpinInterpolation.weight, one_mul, L,
        _root_.smul_apply, _root_.sum_apply,
        _root_.sub_apply, smul_eq_mul, sphereLinear_apply,
        unpack_euclideanDisorder]
  have hilog : Integrable (fun J : Disorder N μ.maxDegree =>
      Real.log (replicatedBandPartition k μ β q δ ρ J m))
      (disorderLaw N μ.maxDegree) := by
    simpa only [Function.comp_def, he] using hic
  exact hilog.div_const _


/-- The samplewise field comparison after projecting a replica tuple to its
exact latitude. The derivative is kept as a single linear functional of the
sum of the transverse offsets. -/
private theorem projected_factor_log_integrable {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q : ℝ} (m : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) (ν : Measure (Vector N))
    [IsFiniteMeasure ν] [NeZero ν]
    (v : Vector N → Vector N) (hv : Measurable v)
    (hnorm : ∀ᵐ σ ∂ν, ‖v σ‖ ^ 2 = (N : ℝ) * (1 - q))
    (ht : ∀ᵐ σ ∂ν, inner ℝ (v σ) m = 0) (β : ℝ) :
    Integrable (fun J : Disorder N μ.maxDegree => Real.log (∫ σ,
      Real.exp (β * taylorRemainderCLM (mixtureCoefficients μ) m (v σ)
        (euclideanDisorder J)) ∂ν)) (disorderLaw N μ.maxDegree) := by
  let L := fun σ => β • taylorRemainderCLM (mixtureCoefficients μ) m (v σ)
  have hL : Measurable L :=
    (projected_taylorRemainderCLM_measurable (mixtureCoefficients μ) m v hv).const_smul β
  have hb : ∀ᵐ σ ∂ν, ‖L σ‖ ≤ |β| * Real.sqrt ((N : ℝ) * residualAtOne μ q) := by
    filter_upwards [hnorm, ht] with σ hσ htσ
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs, physical_taylorRemainder_norm hN μ m (v σ) hm hσ htσ]
  have hi := finite_logPartition_gaussian_integrable ν L hL (by positivity) hb
  have h := (euclideanDisorder_hasLaw N μ.maxDegree).integrable_comp hi
  convert h using 1
  funext J
  simp only [Function.comp_def, GaussianSpinInterpolation.logPartition,
    GaussianSpinInterpolation.moment, GaussianSpinInterpolation.weight, one_mul,
    L, smul_apply, smul_eq_mul]

private theorem projected_factor_pos {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q : ℝ} (m : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) (ν : Measure (Vector N))
    [IsFiniteMeasure ν] [NeZero ν]
    (v : Vector N → Vector N) (hv : Measurable v)
    (hnorm : ∀ᵐ σ ∂ν, ‖v σ‖ ^ 2 = (N : ℝ) * (1 - q))
    (ht : ∀ᵐ σ ∂ν, inner ℝ (v σ) m = 0) (β : ℝ)
    (J : Disorder N μ.maxDegree) :
    Integrable (fun σ => Real.exp
      (β * taylorRemainderCLM (mixtureCoefficients μ) m (v σ) (euclideanDisorder J))) ν ∧
    0 < ∫ σ, Real.exp
      (β * taylorRemainderCLM (mixtureCoefficients μ) m (v σ) (euclideanDisorder J)) ∂ν := by
  let L := fun σ => β • taylorRemainderCLM (mixtureCoefficients μ) m (v σ)
  have hL : Measurable L :=
    (projected_taylorRemainderCLM_measurable (mixtureCoefficients μ) m v hv).const_smul β
  have hb : ∀ᵐ σ ∂ν, |(1 : ℝ)| ≤ 1 ∧
      ‖L σ‖ ≤ |β| * Real.sqrt ((N : ℝ) * residualAtOne μ q) := by
    filter_upwards [hnorm, ht] with σ hσ htσ
    constructor
    · norm_num
    · dsimp only [L]
      rw [norm_smul, Real.norm_eq_abs, physical_taylorRemainder_norm hN μ m (v σ) hm hσ htσ]
  have hi := GaussianSpinInterpolation.weight_integrable ν (fun _ => 1) L
    measurable_const hL hb (euclideanDisorder J)
  have hi' : Integrable (fun σ => Real.exp
      (β * taylorRemainderCLM (mixtureCoefficients μ) m (v σ) (euclideanDisorder J))) ν := by
    exact hi.congr (.of_forall fun σ => by
      change (1 : ℝ) * Real.exp
        ((β • taylorRemainderCLM (mixtureCoefficients μ) m (v σ)) (euclideanDisorder J)) =
          Real.exp (β * taylorRemainderCLM (mixtureCoefficients μ) m (v σ) (euclideanDisorder J))
      rw [one_mul]
      congr 1)
  exact ⟨hi', integral_exp_pos hi'⟩

private theorem replicated_integrand_le {N P k : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) {β d b : ℝ} (hβ : 0 ≤ β)
    (m : Vector N) (σ v : Fin k → Vector N)
    (hm : m ∈ Metric.closedBall 0 (Real.sqrt (N : ℝ)))
    (hσ : ∀ i, σ i ∈ Metric.closedBall 0 (Real.sqrt (N : ℝ)))
    (hp : ∀ i, m + v i ∈ Metric.closedBall 0 (Real.sqrt (N : ℝ)))
    (hd : ∀ i, ‖σ i - (m + v i)‖ ≤ d)
    (hv : ‖∑ i : Fin k, v i‖ ≤ (k : ℝ) * b) :
    Real.exp (β * ∑ i : Fin k, (field c J (σ i) - field c J m)) ≤
      Real.exp ((k : ℝ) * β * physicalBallLipschitzConstant c J * (d + b)) *
        ∏ i : Fin k, Real.exp
          (β * taylorRemainderCLM c m (v i) (euclideanDisorder J)) := by
  let Lip := physicalBallLipschitzConstant c J
  have hL : 0 ≤ Lip := physicalBallLipschitzConstant_nonneg c J
  have hpoint (i : Fin k) : field c J (σ i) - field c J m ≤
      Lip * d + fderiv ℝ (field c J) m (v i) +
        taylorRemainderCLM c m (v i) (euclideanDisorder J) := by
    have hl := (physicalBallLipschitzConstant_lipschitzOn c J).dist_le_mul
      (σ i) (hσ i) (m + v i) (hp i)
    simp only [dist_eq_norm] at hl
    have he : field c J (σ i) - field c J (m + v i) ≤ Lip * d :=
      (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left (hd i) hL))
    rw [taylorRemainderCLM_actual]
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← map_sum] at hsum
  have hder : fderiv ℝ (field c J) m (∑ i : Fin k, v i) ≤ Lip * ((k : ℝ) * b) := by
    have hn := (fderiv ℝ (field c J) m).le_opNorm (∑ i : Fin k, v i)
    rw [Real.norm_eq_abs] at hn
    calc
      _ ≤ ‖fderiv ℝ (field c J) m‖ * ‖∑ i : Fin k, v i‖ := (le_abs_self _).trans hn
      _ ≤ Lip * ((k : ℝ) * b) := mul_le_mul
        (field_fderiv_le_physicalBallLipschitzConstant c J m hm) hv
        (norm_nonneg _) hL
  rw [← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_left hsum hβ
  have hdb := mul_le_mul_of_nonneg_left hder hβ
  dsimp only [Lip] at *
  nlinarith

/-- Dropping the pair constraint factorizes the replicated residual integral.
This is the purely measure-theoretic step in `lem:pc-replica-mean`. -/
private theorem partition_le_factor_power {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {k : ℕ} {B : Set X}
    {T : Set (Fin k → X)} {F : (Fin k → X) → ℝ} {f : X → ℝ} {Λ : ℝ}
    (hsub : T ⊆ univ.pi (fun _ : Fin k => B))
    (hF : IntegrableOn F T (Measure.pi (fun _ : Fin k => ν)))
    (hf : IntegrableOn f B ν) (hf0 : ∀ x, 0 ≤ f x)
    (hpoint : ∀ᵐ σ ∂(Measure.pi (fun _ : Fin k => ν)).restrict T,
      F σ ≤ Real.exp Λ * ∏ i : Fin k, f (σ i)) :
    (∫ σ in T, F σ ∂Measure.pi (fun _ : Fin k => ν)) ≤
      Real.exp Λ * (∫ x in B, f x ∂ν) ^ k := by
  have hp : IntegrableOn (fun σ : Fin k → X => ∏ i, f (σ i))
      (univ.pi (fun _ : Fin k => B)) (Measure.pi (fun _ : Fin k => ν)) := by
    rw [IntegrableOn, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun _ => hf)
  have hpt := hp.mono_set hsub
  calc
    _ ≤ ∫ σ in T, Real.exp Λ * ∏ i : Fin k, f (σ i)
        ∂Measure.pi (fun _ : Fin k => ν) := integral_mono_ae hF
          (hpt.const_mul _) hpoint
    _ ≤ ∫ σ in univ.pi (fun _ : Fin k => B),
        Real.exp Λ * ∏ i : Fin k, f (σ i)
        ∂Measure.pi (fun _ : Fin k => ν) :=
      setIntegral_mono_set (hp.const_mul _)
        (.of_forall fun σ => mul_nonneg (Real.exp_pos _).le
          (Finset.prod_nonneg fun i _ => hf0 (σ i)))
        (.of_forall fun _ h => hsub h)
    _ = _ := by
      rw [integral_const_mul, Measure.restrict_pi_pi, integral_fintype_prod_eq_pow]
      rw [Fintype.card_fin]

/-- Passing a samplewise projected-partition estimate through the original
disorder expectation. Integrability is stated explicitly so all logarithms
are genuine Bochner integrals. -/
private theorem expectedPressure_le_of_partition_bound {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) {β q δ ρ A : ℝ} (m : Vector N)
    (Z : Disorder N μ.maxDegree → ℝ)
    (hZ : ∀ J, 0 < Z J)
    (hP : ∀ J, 0 < replicatedBandPartition k μ β q δ ρ J m)
    (hiP : Integrable (replicatedBandPressure k μ β q δ ρ · m)
      (disorderLaw N μ.maxDegree))
    (hiZ : Integrable (fun J => Real.log (Z J)) (disorderLaw N μ.maxDegree))
    (hbound : ∀ J, replicatedBandPartition k μ β q δ ρ J m ≤
      Real.exp ((k : ℝ) * β * physicalBallLipschitzConstant (mixtureCoefficients μ) J * A) *
        Z J ^ k) :
    expectedReplicatedBandPressure k μ β q δ ρ m ≤
      β * (∫ J, physicalBallLipschitzConstant (mixtureCoefficients μ) J
        ∂disorderLaw N μ.maxDegree) * A / (N : ℝ) +
      (∫ J, Real.log (Z J) ∂disorderLaw N μ.maxDegree) / (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hkr : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hiL := physicalBallLipschitzConstant_integrable hN (mixtureCoefficients μ)
  have hiR : Integrable (fun J =>
      β * physicalBallLipschitzConstant (mixtureCoefficients μ) J * A / (N : ℝ) +
        Real.log (Z J) / (N : ℝ)) (disorderLaw N μ.maxDegree) :=
    (((hiL.const_mul β).mul_const A).div_const _).add (hiZ.div_const _)
  have hb (J : Disorder N μ.maxDegree) :
      replicatedBandPressure k μ β q δ ρ J m ≤
        β * physicalBallLipschitzConstant (mixtureCoefficients μ) J * A / (N : ℝ) +
          Real.log (Z J) / (N : ℝ) := by
    have h := Real.log_le_log (hP J) (hbound J)
    rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (hZ J).ne'),
      Real.log_exp, Real.log_pow] at h
    unfold replicatedBandPressure
    apply (div_le_iff₀ (mul_pos hNr hkr)).mpr
    convert h using 1
    field_simp [hNr.ne', hkr.ne']
  unfold expectedReplicatedBandPressure
  calc
    _ ≤ ∫ J, β * physicalBallLipschitzConstant (mixtureCoefficients μ) J * A / (N : ℝ) +
        Real.log (Z J) / (N : ℝ) ∂disorderLaw N μ.maxDegree := integral_mono hiP hiR hb
    _ = _ := by
      rw [integral_add (((hiL.const_mul β).mul_const A).div_const _)
        (hiZ.div_const _), integral_div, integral_div, integral_mul_const, integral_const_mul]



private theorem physical_projected_logPartition_eq {n : ℕ} (hn : 2 ≤ n)
    (μ : FiniteMixture) (β : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (δ : ℝ) (m : Vector (n + 1)) (hm : ‖m‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * q)
    (hmass : 0 < (sphereLaw (n + 1)).real
      {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q})
    (J : Disorder (n + 1) μ.maxDegree) :
    Real.log (∫ σ in {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q},
      Real.exp (β * taylorRemainderCLM (mixtureCoefficients μ) m
        (Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) • bandDirection q m σ)
        (euclideanDisorder J)) ∂sphereLaw (n + 1)) / ((n + 1 : ℕ) : ℝ) =
      Real.log ((sphereLaw (n + 1)).real
        {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q}) / ((n + 1 : ℕ) : ℝ) +
        transverseResidualPressure μ β q (bandReference q m)
          (latitudeFrameAt (bandReference q m)) J := by
  let u := bandReference q m
  let A : Set ℝ := {a | |a - Real.sqrt q| ≤ δ}
  have hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ) := bandReference_norm_sq q m hq.1 hm
  have hcenter : Real.sqrt q • u = m := bandReference_center q m hq.1
  have hA : MeasurableSet A := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hB : {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q} =
      overlapRegion u A := by
    ext σ
    change |overlap σ m - q| ≤ δ * Real.sqrt q ↔
      |overlap σ u - Real.sqrt q| ≤ δ
    have hscale : overlap σ m = Real.sqrt q * overlap σ u := by
      nth_rw 1 [← hcenter]
      simp only [overlap, real_inner_smul_right]
      ring
    have he : overlap σ m - q = Real.sqrt q * (overlap σ u - Real.sqrt q) := by
      rw [hscale, mul_sub, ← pow_two, Real.sq_sqrt hq.1.le]
    rw [he, abs_mul, abs_of_pos (Real.sqrt_pos.mpr hq.1), mul_comm δ (Real.sqrt q)]
    exact mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hq.1)
  have hsqrt : Real.sqrt q * Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q) / q) =
      Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) := by
    rw [← Real.sqrt_mul hq.1.le]
    congr 1
    field_simp [hq.1.ne']
  have hrem (σ : Vector (n + 1)) :
      taylorRemainderCLM (centerCoefficients (mixtureCoefficients μ) q) u
        (Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q) / q) • planeDirection u σ)
        (euclideanDisorder J) =
      taylorRemainderCLM (mixtureCoefficients μ) m
        (Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) • bandDirection q m σ)
        (euclideanDisorder J) := by
    rw [taylorRemainder_center_scale _ (mixtureCoefficients_nonnegative μ) hq.1.le,
      hcenter, smul_smul, hsqrt]
    rfl
  have hh := projectedResidual_logPartition_eq hn μ β hq u hu hA (by rw [← hB]; exact hmass) J
  simp_rw [hrem] at hh
  rw [← hB] at hh
  exact hh

private theorem sphere_product_support {N k : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N),
      ∀ i : Fin k, ‖σ i‖ ^ 2 = (N : ℝ) :=
  eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin k => sphereLaw N) (i := i)).eventually (sphereLaw_support hN))

private theorem finite_expected_quenched_upper {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (μ : FiniteMixture) {β q δ ρ : ℝ} (hβ : 0 ≤ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 < δ) (hδq : δ ≤ Real.sqrt q / 2)
    (hδ1 : δ ≤ (1 - Real.sqrt q) / 2) (hρ : 0 < ρ)
    (m : Vector (n + 1)) (hm : ‖m‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * q)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw (n + 1)))
      (ReplicatedBand k q δ ρ m)) :
    expectedReplicatedBandPressure k μ β q δ ρ m ≤
      Real.log ((sphereLaw (n + 1)).real
        {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q}) / ((n + 1 : ℕ) : ℝ) +
      expectedTransverseResidualPressure μ β q (bandReference q m)
        (latitudeFrameAt (bandReference q m)) +
      β * (|lipschitzMeanConstant (mixtureCoefficients μ)| + 1) *
        (2 * Real.sqrt δ +
          Real.sqrt (1 / (k : ℝ) + (ρ + Real.sqrt (8 * δ)) / (1 - q))) := by
  have hN : 1 ≤ n + 1 := by omega
  have hN0 : 0 < (n + 1) := by omega
  have hNr : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hN0
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs : 0 < 1 - q := sub_pos.mpr hq.2
  let B : Set (Vector (n + 1)) := {σ | |overlap σ m - q| ≤ δ * Real.sqrt q}
  have hB : MeasurableSet B := (isClosed_le (by unfold overlap; fun_prop)
    continuous_const).measurableSet
  let ν := (sphereLaw (n + 1)).restrict B
  have hmass : 0 < (sphereLaw (n + 1)).real B :=
    oneBand_real_pos_of_replicatedBand_pos hk q δ ρ m hvol
  have hB0 : (sphereLaw (n + 1)) B ≠ 0 := by
    intro h
    simp only [Measure.real, h, ENNReal.toReal_zero] at hmass
    exact (lt_irrefl (0 : ℝ)) hmass
  let : NeZero ((sphereLaw (n + 1)) B) := ⟨hB0⟩
  have : NeZero ν := inferInstance
  let r := (ρ + Real.sqrt (8 * δ)) / (1 - q)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let S := Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q))
  let v : Vector (n + 1) → Vector (n + 1) := fun σ => S • bandDirection q m σ
  have hv : Measurable v := (bandDirection_measurable q m).const_smul S
  have hg : ∀ σ : Vector (n + 1), ‖σ‖ ^ 2 = ((n + 1 : ℕ) : ℝ) → σ ∈ B →
      ‖v σ‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * (1 - q) ∧ inner ℝ (v σ) m = 0 := by
    intro σ hσ hb
    have hgeom := bandDirection_geometry hN0 m σ hq hm hσ hδ.le hδq hδ1 hb
    constructor
    · dsimp only [v]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hgeom.1, one_pow, mul_one]
      exact Real.sq_sqrt (by positivity)
    · dsimp only [v]
      rw [real_inner_smul_left, hgeom.2, mul_zero]
  have hνgeom : ∀ᵐ σ ∂ν,
      ‖v σ‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * (1 - q) ∧ inner ℝ (v σ) m = 0 := by
    filter_upwards [ae_restrict_of_ae (sphereLaw_support hN), ae_restrict_mem hB]
      with σ hσ hb
    exact hg σ hσ hb
  have hvnorm := hνgeom.mono (fun _ h => h.1)
  have hvorth := hνgeom.mono (fun _ h => h.2)
  let Z : Disorder (n + 1) μ.maxDegree → ℝ := fun J => ∫ σ,
    Real.exp (β * taylorRemainderCLM (mixtureCoefficients μ) m (v σ)
      (euclideanDisorder J)) ∂ν
  have hiZ := projected_factor_log_integrable hN0 μ m hm ν v hv hvnorm hvorth β
  have hZ (J : Disorder (n + 1) μ.maxDegree) : 0 < Z J :=
    (projected_factor_pos hN0 μ m hm ν v hv hvnorm hvorth β J).2
  let A := Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * δ) + S * Real.sqrt (1 / (k : ℝ) + r)
  have hA : 0 ≤ A := by dsimp [A, S]; positivity
  have hms : m ∈ Metric.closedBall 0 (Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg (n + 1))).mpr
    rw [hm]
    nlinarith [hq.2]
  have hbound (J : Disorder (n + 1) μ.maxDegree) :
      replicatedBandPartition k μ β q δ ρ J m ≤
        Real.exp ((k : ℝ) * β * physicalBallLipschitzConstant (mixtureCoefficients μ) J * A) *
          Z J ^ k := by
    have hf := (projected_factor_pos hN0 μ m hm ν v hv hvnorm hvorth β J).1
    have hsub : ReplicatedBand k q δ ρ m ⊆ univ.pi (fun _ : Fin k => B) := by
      intro σ hσ i _
      exact hσ.1 i
    have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw (n + 1)),
        ∀ i : Fin k, ‖σ i‖ ^ 2 = ((n + 1 : ℕ) : ℝ) :=
      sphere_product_support hN
    have hpoint : ∀ᵐ σ ∂(Measure.pi (fun _ : Fin k => sphereLaw (n + 1))).restrict
        (ReplicatedBand k q δ ρ m),
        Real.exp (β * ∑ i : Fin k,
          (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m)) ≤
          Real.exp ((k : ℝ) * β * physicalBallLipschitzConstant (mixtureCoefficients μ) J * A) *
            ∏ i : Fin k, Real.exp
              (β * taylorRemainderCLM (mixtureCoefficients μ) m (v (σ i))
                (euclideanDisorder J)) := by
      filter_upwards [ae_restrict_of_ae ha,
        ae_restrict_mem (replicatedBand_measurable q δ ρ m)] with σ hσ hb
      have hω (i : Fin k) : ‖bandDirection q m (σ i)‖ = 1 :=
        (bandDirection_geometry hN0 m (σ i) hq hm (hσ i) hδ.le hδq hδ1 (hb.1 i)).1
      have hpair (i j : Fin k) (hij : i ≠ j) :
          inner ℝ (bandDirection q m (σ i)) (bandDirection q m (σ j)) ≤ r :=
        (le_abs_self _).trans (bandDirection_pair_bound hN0 m (σ i) (σ j) hq hm
          (hσ i) (hσ j) hδ.le hδq hδ1 (hb.1 i) (hb.1 j) (hb.2 i j hij)).le
      have hsum := unitDirections_sum_norm_le hk (fun i => bandDirection q m (σ i))
        hω hr hpair
      have hsumv : ‖∑ i : Fin k, v (σ i)‖ ≤
          (k : ℝ) * (S * Real.sqrt (1 / (k : ℝ) + r)) := by
        simp only [v, ← Finset.smul_sum, norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (show 0 ≤ S by dsimp [S]; positivity)]
        calc
          _ ≤ S * ((k : ℝ) * Real.sqrt (1 / (k : ℝ) + r)) :=
            mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
          _ = _ := by ring
      apply replicated_integrand_le (mixtureCoefficients μ) J hβ m σ
        (fun i => v (σ i)) hms _ _ _ hsumv
      · intro i
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg (n + 1))).mpr (hσ i).le
      · intro i
        simp only [Metric.mem_closedBall, dist_zero_right]
        apply (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg (n + 1))).mpr
        exact (bandProjection_norm_sq hN0 m (σ i) hq hm (hσ i)
          hδ.le hδq hδ1 (hb.1 i)).le
      · intro i
        exact bandProjection_dist_le hN0 m (σ i) hq hm (hσ i)
          hδ.le hδq hδ1 (hb.1 i)
    exact partition_le_factor_power (sphereLaw (n + 1)) hsub
      (replicatedBand_integrand_integrable hN μ β J m).restrict hf
      (fun _ => (Real.exp_pos _).le) hpoint
  have hexpected := expectedPressure_le_of_partition_bound hN hk μ m Z hZ
    (fun J => replicatedBandPartition_pos hN μ β q δ ρ J m hvol)
    (replicatedBandPressure_integrable hN μ β q δ ρ m hvol) hiZ hbound
  let T := fun J : Disorder (n + 1) μ.maxDegree =>
    transverseResidualPressure μ β q (bandReference q m) (latitudeFrameAt (bandReference q m)) J
  let E := Real.log ((sphereLaw (n + 1)).real B) / ((n + 1 : ℕ) : ℝ)
  have hlog (J : Disorder (n + 1) μ.maxDegree) :
      Real.log (Z J) / ((n + 1 : ℕ) : ℝ) = E + T J :=
    physical_projected_logPartition_eq hn μ β hq δ m hm hmass J
  have hT : T = fun J => Real.log (Z J) / ((n + 1 : ℕ) : ℝ) - E := by
    funext J
    linarith [hlog J]
  have hmeanT : expectedTransverseResidualPressure μ β q (bandReference q m)
      (latitudeFrameAt (bandReference q m)) =
      (∫ J, Real.log (Z J) ∂disorderLaw (n + 1) μ.maxDegree) / ((n + 1 : ℕ) : ℝ) - E := by
    change (∫ J, T J ∂disorderLaw (n + 1) μ.maxDegree) = _
    rw [hT, integral_sub (hiZ.div_const _) (integrable_const E), integral_div,
      integral_const, probReal_univ, one_smul]
  have hj' : (∫ J, Real.log (Z J) ∂disorderLaw (n + 1) μ.maxDegree) / ((n + 1 : ℕ) : ℝ) =
      Real.log ((sphereLaw (n + 1)).real B) / ((n + 1 : ℕ) : ℝ) +
        expectedTransverseResidualPressure μ β q (bandReference q m)
          (latitudeFrameAt (bandReference q m)) := by
    dsimp only [E] at hmeanT
    linarith
  let D := |lipschitzMeanConstant (mixtureCoefficients μ)| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hmean : (∫ J, physicalBallLipschitzConstant (mixtureCoefficients μ) J
      ∂disorderLaw (n + 1) μ.maxDegree) ≤ D * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact (expected_physicalBallLipschitzConstant_le hN (mixtureCoefficients μ)).trans
      (mul_le_mul_of_nonneg_right
        (by dsimp [D]; linarith [le_abs_self (lipschitzMeanConstant (mixtureCoefficients μ))])
        (Real.sqrt_nonneg _))
  have hAupper : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (2 * Real.sqrt δ + Real.sqrt (1 / (k : ℝ) + r)) := by
    have hd : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * δ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt δ := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt hNr.le, Real.sq_sqrt hδ.le]
      nlinarith
    have hS : S ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by nlinarith [hq.1])
    have ht := mul_le_mul_of_nonneg_right hS (Real.sqrt_nonneg (1 / (k : ℝ) + r))
    dsimp only [A]
    nlinarith
  have herr : β * (∫ J, physicalBallLipschitzConstant (mixtureCoefficients μ) J
      ∂disorderLaw (n + 1) μ.maxDegree) * A / ((n + 1 : ℕ) : ℝ) ≤
      β * D * (2 * Real.sqrt δ + Real.sqrt (1 / (k : ℝ) + r)) := by
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ β * (D * Real.sqrt ((n + 1 : ℕ) : ℝ)) * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmean hβ) hA
      _ ≤ β * (D * Real.sqrt ((n + 1 : ℕ) : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) * (2 * Real.sqrt δ + Real.sqrt (1 / (k : ℝ) + r))) := by
        gcongr
      _ = _ := by
        have he : Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
          rw [← pow_two, Real.sq_sqrt hNr.le]
        calc
          _ = β * D * (2 * Real.sqrt δ + Real.sqrt (1 / (k : ℝ) + r)) *
              (Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by ring
          _ = _ := by rw [he]
  exact hexpected.trans (by dsimp only [D, B, r] at *; linarith)


private theorem expectedBandUpperApproximation_nonneg
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 ≤ β) :
    ExpectedBandUpperApproximation D := by
  intro q hq ε hε
  let D₀ := |lipschitzMeanConstant (mixtureCoefficients μ)| + 1
  let V := 3 * Real.sqrt q / (2 * (1 - q))
  let C := V + 2 * β * D₀
  have hq0 : 0 < q := hq.1
  have hq1 : 0 < 1 - q := sub_pos.mpr hq.2
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq.1
  have hs1 : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq.1.le, Real.sqrt_nonneg q, hq.2]
  let f : ℝ → ℝ := fun a => C * (Real.sqrt a +
    Real.sqrt (a + (a + Real.sqrt (8 * a)) / (1 - q)))
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hsmall : ∀ᶠ a in 𝓝 (0 : ℝ), f a < ε / 3 :=
    hf.tendsto.eventually_lt_const (by rw [hf0]; positivity)
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp hsmall
  let δ := min (Real.sqrt q / 2) (min ((1 - Real.sqrt q) / 2) (r / 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδq : δ ≤ Real.sqrt q / 2 := min_le_left _ _
  have hδ1 : δ ≤ (1 - Real.sqrt q) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hfδ : f δ < ε / 3 := hnear (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    linarith)
  have hlarge : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ 1 / (k : ℝ) ≤ δ := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ]
      with k hk hi
    exact ⟨hk, hi.le⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlarge
  refine ⟨δ, hδ, δ, hδ, K, ?_⟩
  intro k hk
  obtain ⟨hk1, hi⟩ := hK k hk
  let t := 1 / (k : ℝ) + (δ + Real.sqrt (8 * δ)) / (1 - q)
  have herr : C * (Real.sqrt δ + Real.sqrt t) < ε / 3 := by
    apply lt_of_le_of_lt _ hfδ
    dsimp only [f, t]
    gcongr
  have hent := (tendsto_add_atTop_nat 1).eventually
    (band_entropy_eventually_upper hq hδ hδq hδ1 (by positivity : 0 < ε / 3))
  have hres := expected_transverseResidualPressure_eventually_close_all_real D hq
    (by positivity : 0 < ε / 3)
  have haux : ∀ᶠ n : ℕ in atTop, ∀ m : Vector (n + 1),
      ‖m‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * q →
      0 < (Measure.pi (fun _ : Fin k => sphereLaw (n + 1)))
        (ReplicatedBand k q δ δ m) →
      expectedReplicatedBandPressure k μ β q δ δ m ≤
        Real.log (1 - q) / 2 + D.residual q + ε := by
    filter_upwards [hent, hres, eventually_ge_atTop (2 : ℕ)] with n he hr hn
    intro m hm hvol
    have hmass := oneBand_real_pos_of_replicatedBand_pos hk1 q δ δ m hvol
    have he' := he m hm hmass
    have hfin := finite_expected_quenched_upper hn hk1 μ hβ hq hδ hδq hδ1 hδ m hm hvol
    have hu := bandReference_norm_sq q m hq.1 hm
    have hr' := (abs_lt.mp (hr (bandReference q m) hu
      (latitudeFrameAt (bandReference q m)) (latitudeFrameAt_orthogonal _ hu))).2
    have herror : V * Real.sqrt δ + β * D₀ * (2 * Real.sqrt δ + Real.sqrt t) ≤
        C * (Real.sqrt δ + Real.sqrt t) := by
      dsimp only [C]
      nlinarith [mul_nonneg hV.le (Real.sqrt_nonneg t),
        mul_nonneg (mul_nonneg hβ hD₀.le) (Real.sqrt_nonneg t)]
    change Real.log ((sphereLaw (n + 1)).real
        {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q}) /
        ((n + 1 : ℕ) : ℝ) ≤ Real.log (1 - q) / 2 + V * Real.sqrt δ + ε / 3 at he'
    change expectedReplicatedBandPressure k μ β q δ δ m ≤
      Real.log ((sphereLaw (n + 1)).real
        {σ : Vector (n + 1) | |overlap σ m - q| ≤ δ * Real.sqrt q}) /
        ((n + 1 : ℕ) : ℝ) +
      expectedTransverseResidualPressure μ β q (bandReference q m)
        (latitudeFrameAt (bandReference q m)) +
      β * D₀ * (2 * Real.sqrt δ + Real.sqrt t) at hfin
    linarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp haux
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with N hN
  cases N with
  | zero => omega
  | succ n => exact hn₀ n (by omega)

private theorem replicatedBandPartition_neg_beta {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    replicatedBandPartition k μ (-β) q δ ρ J m =
      replicatedBandPartition k μ β q δ ρ (-J) m := by
  unfold replicatedBandPartition
  apply integral_congr_ae
  exact .of_forall fun σ => by
    dsimp only
    have hs : (∑ i : Fin k,
        (field (mixtureCoefficients μ) (-J) (σ i) -
          field (mixtureCoefficients μ) (-J) m)) =
        -(∑ i : Fin k, (field (mixtureCoefficients μ) J (σ i) -
          field (mixtureCoefficients μ) J m)) := by
      simp only [SourceLiteratureParisiTemperatureEven.field_neg]
      calc
        _ = ∑ i : Fin k, -(field (mixtureCoefficients μ) J (σ i) -
              field (mixtureCoefficients μ) J m) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = _ := by rw [Finset.sum_neg_distrib]
    rw [hs]
    congr 1
    ring

private theorem expectedReplicatedBandPressure_neg_beta {N : ℕ}
    (k : ℕ) (μ : FiniteMixture) (β q δ ρ : ℝ) (m : Vector N) :
    expectedReplicatedBandPressure k μ (-β) q δ ρ m =
      expectedReplicatedBandPressure k μ β q δ ρ m := by
  unfold expectedReplicatedBandPressure replicatedBandPressure
  simp_rw [replicatedBandPartition_neg_beta]
  exact (SourceLiteratureParisiTemperatureEven.disorderLaw_neg_measurePreserving
    N μ.maxDegree).integral_comp'
      (fun J => Real.log (replicatedBandPartition k μ β q δ ρ J m) / ((N : ℝ) * (k : ℝ)))

/-- Subag's quenched band upper approximation, with its exact quantifiers,
for all thermodynamic data and every real inverse temperature. -/
theorem expectedBandUpperApproximation
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) :
    ExpectedBandUpperApproximation D := by
  rcases le_total 0 β with hβ | hβ
  · exact expectedBandUpperApproximation_nonneg D hβ
  · let E : ThermodynamicData μ (-β) :=
      { pressure := D.pressure
        pressure_limit := by
          simpa only [SourceLiteratureParisiTemperatureEven.quenchedPressure_neg]
            using D.pressure_limit
        ground := D.ground
        ground_limit := D.ground_limit
        residual := D.residual
        residual_limit := by
          intro q hq
          simpa only [SourceLiteratureParisiTemperatureEven.quenchedPressure_neg]
            using D.residual_limit q hq }
    have hu := expectedBandUpperApproximation_nonneg E (neg_nonneg.mpr hβ)
    intro q hq ε hε
    obtain ⟨δ, hδ, ρ, hρ, K, hb⟩ := hu q hq ε hε
    refine ⟨δ, hδ, ρ, hρ, K, ?_⟩
    intro k hk
    filter_upwards [hb k hk] with N hN
    intro m hm hvol
    have hh := hN m hm hvol
    change expectedReplicatedBandPressure k μ (-β) q δ ρ m ≤
      Real.log (1 - q) / 2 + D.residual q + ε at hh
    rw [expectedReplicatedBandPressure_neg_beta] at hh
    exact hh

end SlowEquilibration.LiteratureSubagBandUpperFinal
