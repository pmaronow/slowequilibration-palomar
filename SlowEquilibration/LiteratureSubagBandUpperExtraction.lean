-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagRemark25Final
public import SlowEquilibration.LiteratureSubagTheorem5Proof
public import SlowEquilibration.SourceLiteratureGroundStateFinal
public import SlowEquilibration.SphericalTaylorPosteriorPartitionLaw
public import SlowEquilibration.CompactSphereCarrier
public import SlowEquilibration.SphericalResidualTemperatureLimits
public import SlowEquilibration.SphericalLatitudeCoarea
public import SlowEquilibration.ReplicaMeanNetCover
public import SlowEquilibration.SourcePureCaptureReplicaNetGeometry
public import SlowEquilibration.ReplicaBandGibbsMass
public import SlowEquilibration.PhysicalPressureLowerDeviation

/-!
# Further reductions of the quenched band and extraction argument

Subag's band upper estimate uses the quenched Taylor residual, rather than
its annealed upper bound. This file supplies the residual pressure law and
its ambient-dimension limit, uniformly over centers and frames. The comparison
of the thick replicated band with that transverse partition remains unproved.

The exact `SubsequenceBandExtraction` interface is proved. A finite net of
normalized empirical means covers coherent replicas, and Proposition 24,
pressure concentration and ground concentration turn an eventual failure
of extraction into exponential replica decay, contradicting the zero rate.

The ground trial upper bound needs only Chen's finite-temperature formula
and the proved recovery sequences. Consequently the TAP upper inequality,
the quantitative strict gap, and the directing-norm and exponential replica
exclusion reductions here require no Chen--Sen hypothesis. Only the upper
band approximation remains explicit in those partial reductions. Remark 25 also
retains the lower approximation and reconstruction comparison from the
existing Theorem 5 reduction.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandUpperExtraction

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagRemark25Proof LiteratureSubagRemark25Final
open LiteratureSubagTheorem5Proof LiteratureSubagReplicaExclusion
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateRadialCoefficients SourceLiteratureGroundStateCenterBridge
open SphericalTAPCertificate CrisantiSommers
open CSTAPGroundTrialQuadratic CSTAPGroundTrialContactGap CSTAPTelescope
open SourceLiteratureGroundTrialProfile
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SphericalTaylorRemainder SphericalGaussianJet WholeFieldRegression ContinuousFieldLaw

/-- Push the unconditional continuous-field law through the normalized
log-partition, retaining the physical temperature correction. -/
private theorem transverse_logPartition_law
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    [T2Space K] [Nonempty K] {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) (μ : FiniteMixture)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ y, inner ℝ (e y) m = 0)
    (x : K → Vector d) (hx : Continuous x) :
    let c := centerCoefficients (mixtureCoefficients μ) q
    let θ := μ.taylorResidual hq.1 (sub_pos.mpr hq.2)
    let z := fun u => transverseOffset e q (x u)
    let hz : Continuous z := transverseOffset_parameter_continuous e q x hx
    (disorderLaw N μ.maxDegree).map
      (fun J => ContinuousFieldPartition.logPartition ν β
        (taylorContinuousField c m z hz (euclideanDisorder J)) / (N : ℝ)) =
    (disorderLaw d θ.maxDegree).map
      (fun J => ContinuousFieldPartition.logPartition ν (β * Real.sqrt ((N : ℝ) / (d : ℝ)))
        (modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)) / (N : ℝ)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) q
  let θ := μ.taylorResidual hq.1 (sub_pos.mpr hq.2)
  let z := fun u => transverseOffset e q (x u)
  have hz : Continuous z := transverseOffset_parameter_continuous e q x hx
  let X := fun J => taylorContinuousField c m z hz (euclideanDisorder J)
  let Y := fun J : Disorder d θ.maxDegree => Real.sqrt ((N : ℝ) / (d : ℝ)) •
    modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)
  have hX : Measurable X := (taylorContinuousField c m z hz).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  have hY : Measurable Y :=
    ((modelContinuousField (mixtureCoefficients θ) x hx).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)).const_smul (Real.sqrt ((N : ℝ) / (d : ℝ)))
  have hLaw := transverse_taylorContinuousField_law hN hd μ hq m hm e he x hx
  have hp := observable_map_eq _ _ X Y hX hY hLaw
    (fun f => ContinuousFieldPartition.logPartition ν β f / (N : ℝ))
    ((ContinuousFieldPartition.logPartition_measurable ν β).div_const _)
  simpa only [Function.comp_def, X, Y, compact_logPartition_smul] using hp

/-- The literal transverse Taylor remainder integrated against the actual
sphere law, normalized per ambient dimension. The base point has norm
`sqrt N`; the centered coefficient field rescales it to norm `sqrt(Nq)`. -/
def transverseResidualPressure {N d : ℕ} (μ : FiniteMixture) (β q : ℝ)
    (m : Vector N) (e : Vector d →ₗᵢ[ℝ] Vector N)
    (J : Disorder N μ.maxDegree) : ℝ :=
  ContinuousFieldPartition.logPartition (CompactSphereCarrier.law d) β
    (taylorContinuousField (centerCoefficients (mixtureCoefficients μ) q) m
      (fun u : CompactSphereCarrier.Carrier d => transverseOffset e q (u : Vector d))
      (transverseOffset_parameter_continuous e q Subtype.val continuous_subtype_val)
      (euclideanDisorder J)) / (N : ℝ)

/-- Expectation under the original disorder, with no independent residual
disorder substituted in the definition. -/
def expectedTransverseResidualPressure {N d : ℕ} (μ : FiniteMixture) (β q : ℝ)
    (m : Vector N) (e : Vector d →ₗᵢ[ℝ] Vector N) : ℝ :=
  ∫ J : Disorder N μ.maxDegree, transverseResidualPressure μ β q m e J
    ∂disorderLaw N μ.maxDegree

/-- The original-disorder transverse pressure has the exact quenched
residual pressure law in transverse dimension `d`, including `sqrt(N/d)`. -/
theorem transverseResidualPressure_law {N d : ℕ} (hN : 0 < N) (hd : 1 ≤ d)
    (μ : FiniteMixture) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (β : ℝ)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ y, inner ℝ (e y) m = 0) :
    let θ := physicalResidualMixture μ q hq
    (disorderLaw N μ.maxDegree).map (transverseResidualPressure μ β q m e) =
      (disorderLaw d θ.maxDegree).map (fun J =>
        Real.log (mixturePartition θ (β * Real.sqrt ((N : ℝ) / (d : ℝ))) J) / (N : ℝ)) := by
  dsimp only
  let θ := physicalResidualMixture μ q hq
  let ν := CompactSphereCarrier.law d
  let : IsProbabilityMeasure ν := CompactSphereCarrier.law_probability hd
  have hLaw := transverse_logPartition_law hN (by omega : 0 < d) ν β μ hq m hm e he
    (Subtype.val : CompactSphereCarrier.Carrier d → Vector d) continuous_subtype_val
  have hright (J : Disorder d θ.maxDegree) :
      ContinuousFieldPartition.logPartition ν (β * Real.sqrt ((N : ℝ) / (d : ℝ)))
        (modelContinuousField (mixtureCoefficients θ) Subtype.val continuous_subtype_val
          (euclideanDisorder J)) / (N : ℝ) =
      Real.log (mixturePartition θ (β * Real.sqrt ((N : ℝ) / (d : ℝ))) J) / (N : ℝ) := by
    have hc : Continuous (fieldOfMixture θ J) :=
      (field_contDiff (mixtureCoefficients θ) J).continuous
    have heq : modelContinuousField (mixtureCoefficients θ) Subtype.val continuous_subtype_val
        (euclideanDisorder J) =
        (⟨fun u : CompactSphereCarrier.Carrier d => fieldOfMixture θ J u,
          hc.comp continuous_subtype_val⟩ : C(CompactSphereCarrier.Carrier d, ℝ)) := by
      ext u
      exact valueObservation_actual _ _ _
    rw [heq, CompactSphereCarrier.logPartition_eq_sphere hd _ _ hc]
    rfl
  refine hLaw.trans ?_
  exact congrArg (fun f => (disorderLaw d θ.maxDegree).map f) (funext hright)

private theorem transverseResidualPressure_measurable {N d : ℕ} (hd : 1 ≤ d)
    (μ : FiniteMixture) (β q : ℝ) (m : Vector N)
    (e : Vector d →ₗᵢ[ℝ] Vector N) : Measurable (transverseResidualPressure μ β q m e) := by
  let : IsProbabilityMeasure (CompactSphereCarrier.law d) := CompactSphereCarrier.law_probability hd
  exact ((ContinuousFieldPartition.logPartition_measurable (CompactSphereCarrier.law d) β).comp
    ((taylorContinuousField (centerCoefficients (mixtureCoefficients μ) q) m
      (fun u : CompactSphereCarrier.Carrier d => transverseOffset e q (u : Vector d))
      (transverseOffset_parameter_continuous e q Subtype.val continuous_subtype_val)).continuous.measurable.comp
      (euclideanDisorder_measurable _ _))).div_const _

/-- Exact expected quenched residual identity, before any thermodynamic
limit or annealed comparison. -/
theorem expected_transverseResidualPressure_eq {N d : ℕ} (hN : 0 < N) (hd : 1 ≤ d)
    (μ : FiniteMixture) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (β : ℝ)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ y, inner ℝ (e y) m = 0) :
    expectedTransverseResidualPressure μ β q m e =
      ((d : ℝ) / (N : ℝ)) * quenchedPressure d (physicalResidualMixture μ q hq)
        (β * Real.sqrt ((N : ℝ) / (d : ℝ))) := by
  let θ := physicalResidualMixture μ q hq
  have hLaw := transverseResidualPressure_law hN hd μ hq β m hm e he
  have hL := transverseResidualPressure_measurable hd μ β q m e
  have hR : Measurable (fun J : Disorder d θ.maxDegree =>
      Real.log (mixturePartition θ (β * Real.sqrt ((N : ℝ) / (d : ℝ))) J) / (N : ℝ)) :=
    (partition_measurable (N := d) (mixtureCoefficients θ)
      (β * Real.sqrt ((N : ℝ) / (d : ℝ)))).log.div_const (N : ℝ)
  calc
    _ = ∫ t : ℝ, t ∂(disorderLaw N μ.maxDegree).map
        (transverseResidualPressure μ β q m e) :=
      (integral_map (f := fun t : ℝ => t) hL.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ t : ℝ, t ∂(disorderLaw d θ.maxDegree).map
        (fun J => Real.log (mixturePartition θ (β * Real.sqrt ((N : ℝ) / (d : ℝ))) J) / (N : ℝ)) :=
      congrArg (fun ν : Measure ℝ => ∫ t : ℝ, t ∂ν) hLaw
    _ = ∫ J : Disorder d θ.maxDegree,
        Real.log (mixturePartition θ (β * Real.sqrt ((N : ℝ) / (d : ℝ))) J) / (N : ℝ)
          ∂disorderLaw d θ.maxDegree :=
      integral_map (f := fun t : ℝ => t) hR.aemeasurable measurable_id.aestronglyMeasurable
    _ = _ := by
      rw [integral_div, quenchedPressure]
      have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp [hd0, hN0]
      rfl

/-- The unannealed transverse pressure converges to the exact residual
in the encoded thermodynamic data. The canonical pole and frame need
no selection or geometric hypotheses. -/
theorem expected_transverseResidualPressure_tendsto
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 ≤ β) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => expectedTransverseResidualPressure μ β q
      (latitudeChartPole n) (latitudeChartFrame n)) atTop (𝓝 (D.residual q)) := by
  have ht := quenchedPressure_tendsto_dimensionCorrected_per_ambient
    (physicalResidualMixture μ q hq) hβ 1 (D.residual_limit q hq)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have he := expected_transverseResidualPressure_eq (by omega : 0 < n + 1) hn
    μ hq β (latitudeChartPole n) (latitudeChartPole_norm_sq n)
    (latitudeChartFrame n) (latitudeChartFrame_orthogonal n)
  simpa only [dimensionCorrectedTemperature] using he.symm

/-- The residual limit is uniform over every admissible pole and
transverse frame before the dimension limit. -/
theorem expected_transverseResidualPressure_eventually_close
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 ≤ β) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : Vector (n + 1), ‖m‖ ^ 2 = ((n + 1 : ℕ) : ℝ) →
      ∀ e : Vector n →ₗᵢ[ℝ] Vector (n + 1), (∀ y, inner ℝ (e y) m = 0) →
        |expectedTransverseResidualPressure μ β q m e - D.residual q| < ε := by
  have ht := expected_transverseResidualPressure_tendsto D hβ hq
  have ha : Tendsto (fun n : ℕ => |expectedTransverseResidualPressure μ β q
      (latitudeChartPole n) (latitudeChartFrame n) - D.residual q|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (ht.sub (tendsto_const_nhds (x := D.residual q))).abs
  filter_upwards [ha.eventually (gt_mem_nhds hε), eventually_ge_atTop (1 : ℕ)] with n hn hn0
  intro m hm e he
  have hm' := expected_transverseResidualPressure_eq (by omega : 0 < n + 1) hn0 μ hq β m hm e he
  have hp := expected_transverseResidualPressure_eq (by omega : 0 < n + 1) hn0 μ hq β
    (latitudeChartPole n) (latitudeChartPole_norm_sq n)
    (latitudeChartFrame n) (latitudeChartFrame_orthogonal n)
  rw [hm', ← hp]
  exact hn

open SphericalParisiContinuousMaximum PureTensorJetBounds

private def centerMaximum {N : ℕ} (μ : FiniteMixture) (q : ℝ)
    (J : Disorder N μ.maxDegree) : ℝ :=
  sSup ((field (mixtureCoefficients μ) J) ''
    {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q})

private theorem centerMaximum_eq {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q : ℝ} (hq : 0 < q) (J : Disorder N μ.maxDegree) :
    haveI : NeZero N := ⟨hN.ne'⟩
    centerMaximum μ q J = maximum (centerContinuousField μ q N (euclideanDisorder J)) := by
  have : NeZero N := ⟨hN.ne'⟩
  unfold centerMaximum
  rw [centerSphere_sup_eq_scaledMixture μ q hq J, centerMixture_coefficients μ q hq]
  exact sSup_sphere_eq_maximum μ q hN J

private theorem centerMaximum_lipschitz (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 0 < N) :
    haveI : NeZero N := ⟨hN.ne'⟩
    LipschitzWith (Real.sqrt ((N : ℝ) * μ.xi q)).toNNReal
      (fun g => maximum (centerContinuousField μ q N g)) := by
  have : NeZero N := ⟨hN.ne'⟩
  let c := centerCoefficients (mixtureCoefficients μ) q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hq.le
  have hcov : covariancePolynomial c 1 = μ.xi q := by
    dsimp [c]
    rw [covariancePolynomial_center_one, covariancePolynomial_mixture]
  apply LipschitzWith.of_le_add_mul
  intro g h
  obtain ⟨u, hu⟩ := maximum_attained (centerContinuousField μ q N g)
  let x : Vector N := Real.sqrt (N : ℝ) • u.val
  have hx : ‖x‖ ^ 2 = (N : ℝ) := by
    have hun : ‖u.val‖ = 1 := by
      simpa only [PureTensorJetBounds.UnitSphere, Metric.mem_sphere,
        dist_zero_right] using u.property
    simp only [x, norm_smul, Real.norm_eq_abs, sq_abs, hun, mul_one]
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  have heval (z : EuclideanDisorder N μ.maxDegree) :
      centerContinuousField μ q N z u = field c (unpackDisorder z) x := by
    change valueObservation c x z = _
    simp only [valueObservation, flatJetCLM_apply, jet, iteratedFDeriv_zero_apply]
  have hd := field_euclidean_difference_bound (by omega : 1 ≤ N) c hc g h x hx
  rw [hcov] at hd
  have hh := le_maximum (centerContinuousField μ q N h) u
  rw [heval h] at hh
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), hu, heval g]
  linarith [le_abs_self (field c (unpackDisorder g) x - field c (unpackDisorder h) x)]

private theorem centerMaximum_measurable {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q : ℝ} (hq : 0 < q) : Measurable (centerMaximum (N := N) μ q) := by
  have : NeZero N := ⟨hN.ne'⟩
  have heq : centerMaximum (N := N) μ q = fun J =>
      maximum (centerContinuousField μ q N (euclideanDisorder J)) :=
    funext (centerMaximum_eq hN μ hq)
  rw [heq]
  exact (maximum_continuous.comp (centerContinuousField μ q N).continuous).measurable.comp
    (euclideanDisorder_measurable _ _)

private theorem centerMaximum_upper_tail {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    (disorderLaw N μ.maxDegree).real
      {J | expectedCenterGroundEnergy N μ q + t < centerMaximum μ q J / (N : ℝ)} ≤
        2 * Real.exp (-(N : ℝ) * t ^ 2 / (2 * μ.xi q)) := by
  have : NeZero N := ⟨hN.ne'⟩
  let F := fun g : EuclideanDisorder N μ.maxDegree => maximum (centerContinuousField μ q N g)
  let L := Real.sqrt ((N : ℝ) * μ.xi q)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hcov : 0 < μ.xi q := μ.xi_pos hq
  have hLip := centerMaximum_lipschitz μ hq hN
  have hlaw := euclideanDisorder_hasLaw N μ.maxDegree
  have hmean : (∫ J, centerMaximum μ q J ∂disorderLaw N μ.maxDegree) =
      ∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) := by
    calc
      _ = ∫ J, F (euclideanDisorder J) ∂disorderLaw N μ.maxDegree :=
        integral_congr_ae (.of_forall (centerMaximum_eq hN μ hq))
      _ = _ := hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have hcon := SYK.euclidean_lipschitz_gaussian_concentration F L ((N : ℝ) * t)
    (Real.sqrt_pos.mpr (mul_pos hNr hcov)) (mul_pos hNr ht) hLip
  have hset : MeasurableSet {g : EuclideanDisorder N μ.maxDegree |
      |F g - ∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate N μ.maxDegree)| > (N : ℝ) * t} :=
    (isOpen_lt continuous_const (hLip.continuous.sub continuous_const).abs).measurableSet
  nth_rw 1 [← hlaw.map_eq] at hcon
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at hcon
  have hsub : {J : Disorder N μ.maxDegree |
      expectedCenterGroundEnergy N μ q + t < centerMaximum μ q J / (N : ℝ)} ⊆
      euclideanDisorder ⁻¹' {g | |F g - ∫ y, F y
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)| > (N : ℝ) * t} := by
    intro J hJ
    change (N : ℝ) * t < |F (euclideanDisorder J) - _|
    change (N : ℝ) * t < |maximum (centerContinuousField μ q N (euclideanDisorder J)) - _|
    rw [← centerMaximum_eq hN μ hq J, ← hmean]
    change (∫ K, centerMaximum μ q K ∂disorderLaw N μ.maxDegree) / (N : ℝ) + t <
      centerMaximum μ q J / (N : ℝ) at hJ
    have hh : t < (centerMaximum μ q J -
        ∫ K, centerMaximum μ q K ∂disorderLaw N μ.maxDegree) / (N : ℝ) := by
      rw [sub_div]
      linarith
    have hscaled := (lt_div_iff₀ hNr).mp hh
    linarith [le_abs_self (centerMaximum μ q J -
      ∫ K, centerMaximum μ q K ∂disorderLaw N μ.maxDegree)]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcon
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  have hrate : -((N : ℝ) * t) ^ 2 / (2 * L ^ 2) = -(N : ℝ) * t ^ 2 / (2 * μ.xi q) := by
    dsimp [L]
    rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hcov.le)]
    field_simp
  rw [hrate] at hr
  exact (measureReal_mono hsub).trans hr

private theorem field_le_centerMaximum {N : ℕ} (μ : FiniteMixture) {q : ℝ}
    (hq : 0 ≤ q) (J : Disorder N μ.maxDegree) (m : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) : field (mixtureCoefficients μ) J m ≤ centerMaximum μ q J := by
  have hs : {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q} =
      Metric.sphere 0 (Real.sqrt ((N : ℝ) * q)) := by
    ext m
    constructor
    · intro hm
      simp only [Metric.mem_sphere, dist_zero_right]
      rw [← Real.sqrt_sq (norm_nonneg m), hm]
    · intro hm
      change ‖m‖ ^ 2 = (N : ℝ) * q
      have hn : ‖m‖ = Real.sqrt ((N : ℝ) * q) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hm
      rw [hn, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hq)]
  have hcompact : IsCompact {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q} := by
    rw [hs]
    exact isCompact_sphere 0 _
  exact le_csSup (hcompact.image (field_contDiff (mixtureCoefficients μ) J).continuous).bddAbove
    ⟨m, hm, rfl⟩

/-- General-mixture ground concentration supplies a measurable event
controlling the original field simultaneously on the full center sphere.
The rate and error are fixed before the dimension limit. -/
theorem ground_upper_good_events {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ N : ℕ in atTop, ∃ G : Set (Disorder N μ.maxDegree),
      MeasurableSet G ∧ (disorderLaw N μ.maxDegree).real Gᶜ ≤
        2 * Real.exp (-(t ^ 2 / (8 * μ.xi q)) * (N : ℝ)) ∧
      ∀ J ∈ G, ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
        field (mixtureCoefficients μ) J m / (N : ℝ) ≤ D.ground q + t := by
  have hmean : ∀ᶠ N : ℕ in atTop, expectedCenterGroundEnergy N μ q < D.ground q + t / 2 :=
    (D.ground_limit q hq).eventually_lt_const (by linarith)
  filter_upwards [hmean, eventually_gt_atTop (0 : ℕ)] with N hm hN
  let G : Set (Disorder N μ.maxDegree) :=
    {J | centerMaximum μ q J / (N : ℝ) ≤ D.ground q + t}
  refine ⟨G, measurableSet_le ((centerMaximum_measurable hN μ hq.1).div_const _) measurable_const,
    ?_, ?_⟩
  · have hb := centerMaximum_upper_tail hN μ hq.1 (by linarith : 0 < t / 2)
    have hs : Gᶜ ⊆ {J | expectedCenterGroundEnergy N μ q + t / 2 <
        centerMaximum μ q J / (N : ℝ)} := by
      intro J hJ
      change expectedCenterGroundEnergy N μ q + t / 2 < centerMaximum μ q J / (N : ℝ)
      have hh : D.ground q + t < centerMaximum μ q J / (N : ℝ) := lt_of_not_ge hJ
      linarith
    apply (measureReal_mono hs).trans
    have heq : -(t ^ 2 / (8 * μ.xi q)) * (N : ℝ) =
        -(N : ℝ) * (t / 2) ^ 2 / (2 * μ.xi q) := by ring
    simpa only [heq] using hb
  · intro J hJ m hnorm
    exact (div_le_div_of_nonneg_right (field_le_centerMaximum μ hq.1.le J m hnorm)
      (Nat.cast_nonneg N)).trans hJ

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



private theorem bandPressure_mono {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ₁ δ₂ ρ₁ ρ₂ : ℝ) (m : Vector N)
    (hδ : δ₁ ≤ δ₂) (hρ : ρ₁ ≤ ρ₂)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ₁ ρ₁ m)) :
    expectedReplicatedBandPressure k μ β q δ₁ ρ₁ m ≤
      expectedReplicatedBandPressure k μ β q δ₂ ρ₂ m := by
  have hsub : ReplicatedBand k q δ₁ ρ₁ m ⊆ ReplicatedBand k q δ₂ ρ₂ m := by
    intro σ hσ
    refine ⟨fun i => (hσ.1 i).trans ?_, fun i j hij => (hσ.2 i j hij).trans_le hρ⟩
    exact mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg q)
  have hvol₂ : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ₂ ρ₂ m) := hvol.trans_le (measure_mono hsub)
  unfold expectedReplicatedBandPressure
  apply integral_mono (replicatedBandPressure_integrable hN μ β q δ₁ ρ₁ m hvol)
    (replicatedBandPressure_integrable hN μ β q δ₂ ρ₂ m hvol₂)
  intro J
  have hpart : replicatedBandPartition k μ β q δ₁ ρ₁ J m ≤
      replicatedBandPartition k μ β q δ₂ ρ₂ J m := by
    unfold replicatedBandPartition
    exact setIntegral_mono_set (replicatedBand_integrand_integrable hN μ β J m).restrict
      (.of_forall fun _ => (Real.exp_pos _).le) (.of_forall fun _ h => hsub h)
  unfold replicatedBandPressure
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (replicatedBandPartition_pos hN μ β q δ₁ ρ₁ J m hvol) hpart)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

open LiteratureSubagTheorem10Proof LiteratureSubagProposition24
open MixedCapturePhysicalReplicaGeometry SphericalAging.HardSphereDynamics

private theorem coherent_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem expected_block_eq_integral (N k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) :
    expectedOverlapBlockProbability N k μ β q ρ =
      ∫ J, conditionalBlockProbability N k μ β q ρ J ∂disorderLaw N μ.maxDegree := by
  unfold expectedOverlapBlockProbability GaussianReplicaKernel.law
    conditionalBlockProbability Measure.real
  rw [integral_toReal]
  · exact congrArg ENNReal.toReal
      (Measure.bind_apply (coherent_measurable q ρ) (Kernel.aemeasurable _))
  · exact (Kernel.measurable_coe _ (coherent_measurable q ρ)).aemeasurable
  · exact .of_forall fun _ => measure_lt_top _ _

private theorem expected_block_le_failure {N k : ℕ} (μ : FiniteMixture) (β q ρ : ℝ)
    (G : Set (Disorder N μ.maxDegree)) (hG : MeasurableSet G) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ J ∈ G,
      (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (overlapBlock q ρ) ≤ b) :
    expectedOverlapBlockProbability N k μ β q ρ ≤
      (disorderLaw N μ.maxDegree).real Gᶜ + b := by
  rw [expected_block_eq_integral]
  have hi : Integrable (Gᶜ.indicator (fun _ => (1 : ℝ))) (disorderLaw N μ.maxDegree) :=
    (integrable_const 1).indicator hG.compl
  have hp : Integrable (conditionalBlockProbability N k μ β q ρ) (disorderLaw N μ.maxDegree) :=
    Kernel.IsMarkovKernel.integrable _ _ (coherent_measurable q ρ)
  calc
    _ ≤ ∫ J, Gᶜ.indicator (fun _ => (1 : ℝ)) J + b ∂disorderLaw N μ.maxDegree := by
      apply integral_mono hp (hi.add (integrable_const b))
      intro J
      change conditionalBlockProbability N k μ β q ρ J ≤
        Gᶜ.indicator (fun _ => (1 : ℝ)) J + b
      by_cases hJ : J ∈ G
      · rw [Set.indicator_of_notMem (show J ∉ Gᶜ from not_not_intro hJ), zero_add]
        simpa only [conditionalBlockProbability, GaussianReplicaKernel.iid_apply,
          allDimensionGibbsKernel_apply] using hbound J hJ
      · rw [Set.indicator_of_mem (show J ∈ Gᶜ from hJ)]
        exact measureReal_le_one.trans (by linarith)
    _ = _ := by
      rw [integral_add hi (integrable_const b), integral_indicator_const (1 : ℝ) hG.compl]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one]

private theorem extraction_parameters {q ε δ ρ δ₀ ρ₀ : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hδ₀ : 0 < δ₀) (hρ₀ : 0 < ρ₀) (K k₀ : ℕ) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ δ₀ ∧
      ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ρ' ≤ ρ₀ ∧
        ∃ θ η : ℝ, 0 < θ ∧ 0 < η ∧ η < q / 2 ∧ η ≤ ρ' ∧
          ∃ k : ℕ, max K 1 ≤ k ∧ k₀ ≤ k ∧
            (2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ) + θ ≤ δ' * Real.sqrt q ∧
            Real.log (1 + 2 * Real.sqrt q / θ) ≤ (k : ℝ) * ε / 8 := by
  let δ' := min δ δ₀
  let ρ' := min ρ ρ₀
  have hδ' : 0 < δ' := by dsimp [δ']; positivity
  have hρ' : 0 < ρ' := by dsimp [ρ']; positivity
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  let θ := δ' * Real.sqrt q / 4
  let η := min (q / 4) (min (ρ' / 2) (δ' * Real.sqrt q / 32))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηq : η < q / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηρhalf : η ≤ ρ' / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηρ : η ≤ ρ' := by linarith
  have hηδ : η ≤ δ' * Real.sqrt q / 32 := (min_le_right _ _).trans (min_le_right _ _)
  let A := Real.log (1 + 2 * Real.sqrt q / θ)
  obtain ⟨B, hB⟩ := exists_nat_gt (8 * A / ε)
  have hlarge : ∀ᶠ k : ℕ in atTop,
      K ≤ k ∧ k₀ ≤ k ∧ 1 ≤ k ∧ 1 / (k : ℝ) ≤ δ' * Real.sqrt q / 4 ∧ B ≤ k := by
    filter_upwards [eventually_ge_atTop K, eventually_ge_atTop k₀,
      eventually_ge_atTop (1 : ℕ),
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const
        (show 0 < δ' * Real.sqrt q / 4 by positivity), eventually_ge_atTop B]
      with k hK hk₀ hk1 hi hBk
    exact ⟨hK, hk₀, hk1, hi.le, hBk⟩
  obtain ⟨k, hK, hk₀, hk1, hi, hBk⟩ := hlarge.exists
  refine ⟨δ', hδ', min_le_left _ _, min_le_right _ _,
    ρ', hρ', min_le_left _ _, min_le_right _ _, θ, η,
    hθ, hη, hηq, hηρ, k, max_le hK hk1, hk₀, ?_, ?_⟩
  · have hc : 2 * Real.sqrt 2 + 1 ≤ 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hcη := mul_le_mul_of_nonneg_right hc hη.le
    dsimp only [θ]
    nlinarith [mul_pos hδ' hs]
  · have hcast : (B : ℝ) ≤ k := by exact_mod_cast hBk
    have hh : 8 * A / ε ≤ (k : ℝ) := hB.le.trans hcast
    have hh' := (div_le_iff₀ hε).mp hh
    change A ≤ (k : ℝ) * ε / 8
    nlinarith

private theorem coherent_net_cover {N k M : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {q η δ ρ θ : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hη : 0 ≤ η)
    (hηq : η < q / 2) (hηρ : η ≤ ρ)
    (hgeometry : (2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ) + θ ≤ δ * Real.sqrt q)
    (points : Fin M → Vector N)
    (hnet : ∀ m : Vector N, ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt q →
      ∃ j, ‖m - points j‖ ≤ θ * Real.sqrt (N : ℝ))
    (σ : Fin k → Vector N) (hσ : ∀ i, ‖σ i‖ ^ 2 = (N : ℝ))
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < η) :
    ∃ j, σ ∈ ReplicatedBand k q δ ρ (points j) := by
  have hσ' : ∀ i, OnSphere (σ i) := fun i => (onSphere_iff_norm_sq _).mpr (hσ i)
  have hcm := physicalContactMean_norm_sq hN (by omega) σ hσ' hq hη hηq
    (fun i j hij => (hpair i j hij).le)
  have hcmnorm : ‖physicalContactMean q σ‖ = Real.sqrt (N : ℝ) * Real.sqrt q := by
    rw [← Real.sqrt_sq (norm_nonneg (physicalContactMean q σ)), hcm,
      Real.sqrt_mul (Nat.cast_nonneg N)]
  obtain ⟨j, hj⟩ := hnet _ hcmnorm
  refine ⟨j, ReplicaMeanNetCover.mem_replicatedBand_of_near_contactMean hN hk hq hη hηq hηρ
    hgeometry σ hσ' hpair (points j) ?_⟩
  simpa only [norm_sub_rev] using hj

private theorem coherent_on_event_gibbs_bound {N k M : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) {β q η δ ρ E F ε A : ℝ} (hβ : 0 < β)
    (points : Fin M → Vector N) (hM : 0 < M)
    (hnorm : ∀ j, ‖points j‖ ^ 2 = (N : ℝ) * q)
    (hcard : Real.log (M : ℝ) ≤ (N : ℝ) * A) (hbeat : A ≤ (k : ℝ) * ε / 8)
    (J : Disorder N μ.maxDegree)
    (hcover : ∀ σ : Fin k → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      (∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < η) →
      ∃ j, σ ∈ ReplicatedBand k q δ ρ (points j))
    (hground : ∀ j, field (mixtureCoefficients μ) J (points j) / (N : ℝ) ≤ E + ε / (8 * β))
    (hpressure : F - ε / 8 ≤ Real.log (mixturePartition μ β J) / (N : ℝ))
    (hupper : ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
      replicatedBandPressure k μ β q δ ρ J m <
        expectedReplicatedBandPressure k μ β q δ ρ m + ε / 8)
    (hexpected : ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
      0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k q δ ρ m) →
      expectedReplicatedBandPressure k μ β q δ ρ m < F - β * E - ε) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
      (overlapBlock q η) ≤ Real.exp (-(N : ℝ) * (k : ℝ) * ε / 2) := by
  classical
  let π := gibbsLaw N β (field (mixtureCoefficients μ) J)
  let ν := Measure.pi (fun _ : Fin k => π)
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β (field_contDiff _ J).continuous
  let B : Fin M → Set (Fin k → Vector N) := fun j => ReplicatedBand k q δ ρ (points j)
  have ha : ∀ᵐ σ ∂ν, ∀ i, ‖σ i‖ ^ 2 = (N : ℝ) :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin k => π) (i := i)).eventually
      (gibbsLaw_support hN β (field (mixtureCoefficients μ) J)))
  have hsub : overlapBlock q η ≤ᵐ[ν] ⋃ j, B j := by
    filter_upwards [ha] with σ hσ hl
    obtain ⟨j, hj⟩ := hcover σ hσ hl
    exact mem_iUnion.mpr ⟨j, hj⟩
  have hband (j : Fin M) : ν.real (B j) ≤
      Real.exp (-(N : ℝ) * (k : ℝ) * (5 * ε / 8)) := by
    by_cases hv : (Measure.pi (fun _ : Fin k => sphereLaw N)) (B j) = 0
    · rw [show ν.real (B j) = 0 from
        ReplicaBandGibbsMass.productGibbs_band_eq_zero_of_volume_zero hN μ β q δ ρ J (points j) hv]
      exact (Real.exp_pos _).le
    · have hA : replicatedBandPressure k μ β q δ ρ J (points j) < F - β * E - 7 * ε / 8 := by
        have hu := hupper _ (hnorm j)
        have hx := hexpected _ (hnorm j) (pos_iff_ne_zero.mpr hv)
        linarith
      have hb := ReplicaBandGibbsMass.productGibbs_band_le hN hk μ β q δ ρ J (points j) hA
      apply hb.trans (Real.exp_le_exp.mpr ?_)
      have he' : β * field (mixtureCoefficients μ) J (points j) / (N : ℝ) ≤ β * E + ε / 8 := by
        have ht := mul_le_mul_of_nonneg_left (hground j) hβ.le
        have heq : β * (E + ε / (8 * β)) = β * E + ε / 8 := by field_simp [hβ.ne']
        rw [heq] at ht
        simpa only [mul_div_assoc] using ht
      have hh : β * field (mixtureCoefficients μ) J (points j) / (N : ℝ) +
          (F - β * E - 7 * ε / 8) - Real.log (mixturePartition μ β J) / (N : ℝ) ≤
            -(5 * ε / 8) := by linarith
      calc
        _ ≤ (N : ℝ) * (k : ℝ) * (-(5 * ε / 8)) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ν.real (⋃ j, B j) := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ j, ν.real (B j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin M, Real.exp (-(N : ℝ) * (k : ℝ) * (5 * ε / 8)) :=
      Finset.sum_le_sum (fun j _ => hband j)
    _ = (M : ℝ) * Real.exp (-(N : ℝ) * (k : ℝ) * (5 * ε / 8)) := by simp
    _ ≤ Real.exp ((N : ℝ) * A) * Real.exp (-(N : ℝ) * (k : ℝ) * (5 * ε / 8)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [← Real.exp_log (Nat.cast_pos.mpr hM)]
      exact Real.exp_le_exp.mpr hcard
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hbeat (Nat.cast_nonneg N)
      nlinarith

private theorem extraction_error_sum {cp cg t : ℝ} (hcp : 0 < cp) (hcg : 0 < cg) (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      Real.exp (-(N : ℝ)) + 2 * Real.exp (-cp * (N : ℝ)) +
        2 * Real.exp (-cg * (N : ℝ)) + Real.exp (-t * (N : ℝ)) ≤
          Real.exp (-c * (N : ℝ)) := by
  let b : ℝ := min 1 (min cp (min cg t))
  have hb : 0 < b := lt_min (by norm_num) (lt_min hcp (lt_min hcg ht))
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbp : b ≤ cp := (min_le_right _ _).trans (min_le_left _ _)
  have hbg : b ≤ cg := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbt : b ≤ t := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let c := b / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hexp : Tendsto (fun N : ℕ => Real.exp (-c * (N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  refine ⟨c, hc, ?_⟩
  filter_upwards [hexp.eventually_lt_const (show (0 : ℝ) < 1 / 6 by norm_num)] with N hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : Real.exp (-(N : ℝ)) ≤ Real.exp (-b * (N : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
  have hp : Real.exp (-cp * (N : ℝ)) ≤ Real.exp (-b * (N : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
  have hg : Real.exp (-cg * (N : ℝ)) ≤ Real.exp (-b * (N : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
  have ht' : Real.exp (-t * (N : ℝ)) ≤ Real.exp (-b * (N : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
  have hsq : Real.exp (-b * (N : ℝ)) = Real.exp (-c * (N : ℝ)) * Real.exp (-c * (N : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [c]
    ring
  calc
    _ ≤ 6 * Real.exp (-b * (N : ℝ)) := by linarith
    _ = (6 * Real.exp (-c * (N : ℝ))) * Real.exp (-c * (N : ℝ)) := by rw [hsq]; ring
    _ ≤ 1 * Real.exp (-c * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = _ := one_mul _

/-- Section 4's extraction, with the exact original quantifiers. A finite
net of normalized empirical means replaces conditional replica selection.
Uniform concentration and the actual pressure and ground limits rule out
an eventual deficit for every positive-volume band. -/
theorem subsequenceBandExtraction {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : SubsequenceBandExtraction D := by
  classical
  intro q hq h24 φ hφ hm ε δ ρ hε hδ hρ K
  have hβ : 0 < β := h24.1
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, k₀, hcon⟩ :=
    fixedParameters_uniform_upper μ β q h24 (t := ε / 8) (c := 1)
      (by positivity) (by norm_num)
  obtain ⟨δ', hδ', hδ'δ, hδ'₀, ρ', hρ', hρ'ρ, hρ'₀, θ, η,
      hθ, hη, hηq, hηρ, k, hk, hkk₀, hgeometry, hbeat⟩ :=
    extraction_parameters hq.1 hε hδ hρ hδ₀ hρ₀ K k₀
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  refine ⟨k, hk, ?_⟩
  by_contra hnot
  have hfail : ∀ᶠ n : ℕ in atTop,
      ¬ ∃ m : Vector (φ n), ‖m‖ ^ 2 = (φ n : ℝ) * q ∧
        0 < (Measure.pi (fun _ : Fin k => sphereLaw (φ n))) (ReplicatedBand k q δ ρ m) ∧
        D.pressure - β * D.ground q - ε ≤ expectedReplicatedBandPressure k μ β q δ ρ m :=
    not_frequently.mp hnot
  let cp := (ε / 8) ^ 2 / (8 * β ^ 2 * μ.xi 1)
  let cg := (ε / (8 * β)) ^ 2 / (8 * μ.xi q)
  have hxi1 : 0 < μ.xi 1 := μ.xi_pos zero_lt_one
  have hxiq : 0 < μ.xi q := μ.xi_pos hq.1
  have hcp : 0 < cp := by dsimp [cp]; positivity
  have hcg : 0 < cg := by dsimp [cg]; positivity
  have hpressure := PhysicalPressureLowerDeviation.pressure_lower_deviation_exponential μ hβ
    D.pressure_limit (t := ε / 8) (by positivity)
  have hground := ground_upper_good_events D hq (t := ε / (8 * β)) (by positivity)
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨c, hc, herrors⟩ := extraction_error_sum hcp hcg
    (show 0 < (k : ℝ) * ε / 2 by positivity)
  have hbound : ∀ᶠ n : ℕ in atTop,
      expectedOverlapBlockProbability (φ n) k μ β q η ≤ Real.exp (-c * (φ n : ℝ)) := by
    filter_upwards [hfail, hφ.tendsto_atTop.eventually (eventually_ge_atTop (k + 1)),
      hφ.tendsto_atTop.eventually hground, hφ.tendsto_atTop.eventually hpressure,
      hφ.tendsto_atTop.eventually herrors] with n hfailN hN hg hp he
    have hN1 : 1 ≤ φ n := by omega
    obtain ⟨Gg, hGg, hGgfail, hGgfield⟩ := hg
    obtain ⟨Ω, hΩ, hΩprob, hΩupper⟩ :=
      hcon δ' hδ' hδ'₀ ρ' hρ' hρ'₀ k hkk₀ (φ n) hN
    let B : Set (Disorder (φ n) μ.maxDegree) :=
      {J | Real.log (mixturePartition μ β J) / (φ n : ℝ) < D.pressure - ε / 8}
    let G : Set (Disorder (φ n) μ.maxDegree) := Gg ∩ Bᶜ ∩ Ω
    have hB : MeasurableSet B := PhysicalPressureLowerDeviation.pressure_lower_deviation_measurable
      μ β D.pressure (ε / 8) (φ n)
    have hG : MeasurableSet G := (hGg.inter hB.compl).inter hΩ
    have hΩfail : (disorderLaw (φ n) μ.maxDegree).real Ωᶜ ≤ Real.exp (-(φ n : ℝ)) := by
      rw [measureReal_compl hΩ, probReal_univ]
      have hh : 1 - Real.exp (-(φ n : ℝ)) < (disorderLaw (φ n) μ.maxDegree).real Ω := by
        simpa only [neg_one_mul] using hΩprob
      linarith
    have hGfail : (disorderLaw (φ n) μ.maxDegree).real Gᶜ ≤
        Real.exp (-(φ n : ℝ)) + 2 * Real.exp (-cp * (φ n : ℝ)) +
          2 * Real.exp (-cg * (φ n : ℝ)) := by
      have hu : (disorderLaw (φ n) μ.maxDegree).real Gᶜ ≤
          (disorderLaw (φ n) μ.maxDegree).real Ggᶜ +
            (disorderLaw (φ n) μ.maxDegree).real B +
              (disorderLaw (φ n) μ.maxDegree).real Ωᶜ := by
        simp only [G, compl_inter, compl_compl]
        apply (measureReal_union_le _ _).trans
        have hh := measureReal_union_le (μ := disorderLaw (φ n) μ.maxDegree) Ggᶜ B
        linarith
      change (disorderLaw (φ n) μ.maxDegree).real B ≤ 2 * Real.exp (-cp * (φ n : ℝ)) at hp
      change (disorderLaw (φ n) μ.maxDegree).real Ggᶜ ≤ 2 * Real.exp (-cg * (φ n : ℝ)) at hGgfail
      linarith
    obtain ⟨M, points, hM, hnorm, hnet, hcard⟩ :=
      SourcePureCaptureReplicaNetGeometry.exists_physical_center_net (φ n) (by omega) hq.1 hθ
    have hnormsq : ∀ j, ‖points j‖ ^ 2 = (φ n : ℝ) * q := by
      intro j
      rw [hnorm j, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hq.1.le]
    have hcover := coherent_net_cover hN1 hk1 hq hη.le hηq hηρ hgeometry points hnet
    have hexpected : ∀ m : Vector (φ n), ‖m‖ ^ 2 = (φ n : ℝ) * q →
        0 < (Measure.pi (fun _ : Fin k => sphereLaw (φ n))) (ReplicatedBand k q δ' ρ' m) →
        expectedReplicatedBandPressure k μ β q δ' ρ' m < D.pressure - β * D.ground q - ε := by
      intro m hmN hv
      have hsub : ReplicatedBand k q δ' ρ' m ⊆ ReplicatedBand k q δ ρ m := by
        intro σ hσ
        exact ⟨fun i => (hσ.1 i).trans
          (mul_le_mul_of_nonneg_right hδ'δ (Real.sqrt_nonneg q)),
          fun i j hij => (hσ.2 i j hij).trans_le hρ'ρ⟩
      have hvbig := hv.trans_le (measure_mono hsub)
      have hn : ¬ D.pressure - β * D.ground q - ε ≤ expectedReplicatedBandPressure k μ β q δ ρ m :=
        fun hl => hfailN ⟨m, hmN, hvbig, hl⟩
      exact (bandPressure_mono hN1 μ β q δ' δ ρ' ρ m hδ'δ hρ'ρ hv).trans_lt (lt_of_not_ge hn)
    have hconditional : ∀ J ∈ G,
        (Measure.pi (fun _ : Fin k => gibbsLaw (φ n) β (field (mixtureCoefficients μ) J))).real
          (overlapBlock q η) ≤ Real.exp (-(φ n : ℝ) * (k : ℝ) * ε / 2) := by
      intro J hJG
      obtain ⟨⟨hJg, hJp⟩, hJΩ⟩ := hJG
      exact coherent_on_event_gibbs_bound hN1 hk1 μ hβ points hM hnormsq hcard hbeat J
        hcover (fun j => hGgfield J hJg _ (hnormsq j))
        (le_of_not_gt hJp) (hΩupper J hJΩ) hexpected
    have hb := expected_block_le_failure μ β q η G hG (Real.exp_nonneg _) hconditional
    have heq : -(φ n : ℝ) * (k : ℝ) * ε / 2 = -((k : ℝ) * ε / 2) * (φ n : ℝ) := by ring
    rw [heq] at hb
    linarith
  obtain ⟨hpos, hlim⟩ := hm k hk1 η hη
  have hrate : ∀ᶠ n : ℕ in atTop,
      -c < Real.log (expectedOverlapBlockProbability (φ n) k μ β q η) / (φ n : ℝ) :=
    hlim.eventually (lt_mem_nhds (neg_neg_of_pos hc))
  obtain ⟨n, hbn, hpn, hrn, hNn⟩ := (hbound.and (hpos.and (hrate.and
    (hφ.tendsto_atTop.eventually (eventually_gt_atTop (0 : ℕ)))))).exists
  have hNr : 0 < (φ n : ℝ) := Nat.cast_pos.mpr hNn
  have hlog : -c * (φ n : ℝ) < Real.log (expectedOverlapBlockProbability (φ n) k μ β q η) :=
    (lt_div_iff₀ hNr).mp hrn
  exact (not_lt_of_ge hbn) ((Real.lt_log_iff_exp_lt hpn).mp hlog)

/-- The upper variational bound for the actual center ground limit follows
from finite-temperature minimization and recovery; no minimizing ground
profile or compactness theorem is required. -/
theorem center_ground_le_profile (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1) (v : GroundProfile) :
    D.ground q ≤ groundFunctional (centerMixture μ q hq.1) v := by
  obtain ⟨E, hGround, hCS⟩ :=
    SourceLiteratureGroundStateProof.exists_ground_and_zero_temperature_limits hChen
      (centerMixture μ q hq.1)
  have hcenter : Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q)
      atTop (𝓝 E) := hGround.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (expectedCenterGroundEnergy_eq_canonical μ hq.1 hN).symm)
  have hE : D.ground q = E := tendsto_nhds_unique (D.ground_limit q hq) hcenter
  rw [hE]
  obtain ⟨ζ, hζ⟩ := SourceLiteratureGroundStateFinal.groundRecoverySequences
    (centerMixture μ q hq.1) v
  have hτ : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  apply le_of_tendsto_of_tendsto (hCS.comp hτ) hζ
  exact .of_forall fun n => div_le_div_of_nonneg_right
    (CSParisiMeasure.canonicalMinimizer_isMinimizer
      (centerMixture μ q hq.1) ((n + 1 : ℕ) : ℝ) (ζ n)) (by positivity)

/-- The general TAP upper inequality from Chen alone, without either
band approximation, reconstruction, or Subag interface. -/
theorem tapValue_le_pressure_reduced3 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β) (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1) : tapValue D q ≤ D.pressure := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  have hground : D.ground q ≤
      CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 := by
    rw [← SourceGeneralContactTheorem.radiusFunctional_groundTrial μ ζ hβ hq
      (le_refl (0 : ℝ)), SourceGroundProfileUniqueness.radiusFunctional_eq_normalize μ hq.1]
    exact center_ground_le_profile hChen D hq _
  have hres : D.residual q ≤
      (SourceGeneralTAPTelescope.residualTrial ζ hq).value β
        (CSTAPTelescope.residualMixture μ hq).xi := by
    have hR := tendsto_nhds_unique (D.residual_limit q hq)
      (hChen (physicalResidualMixture μ q hq) β hβ.le)
    rw [hR]
    exact CSParisiMeasure.canonicalMinimizer_isMinimizer _ β _
  have hP := tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have htel := SourceGeneralTAPTelescope.canonical_telescope μ hβ hq
  have hβg := mul_le_mul_of_nonneg_left hground hβ.le
  unfold tapValue
  rw [hP, htel]
  change β * D.ground q + Real.log (1 - q) / 2 + D.residual q ≤
    β * CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 + Real.log (1 - q) / 2 +
      (SourceGeneralTAPTelescope.residualTrial ζ hq).value β
        (CSTAPTelescope.residualMixture μ hq).xi
  linarith

/-- The quantitative manuscript TAP gap uses a recovery trial only, so
Chen--Sen's ground minimizer identification can be removed. -/
theorem tapValue_le_pressure_sub_gap_reduced3 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (D : ThermodynamicData μ β) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≠ Q) :
    tapValue D q ≤ D.pressure -
      (CSStructure.potential μ β (twoAtom x Q) q) ^ 2 /
        (8 * β ^ 3 * curvature β (twoAtom x Q) q) := by
  have hβ := h.beta_pos
  have hP : D.pressure = CSParisiMeasure.variationalValue μ β :=
    tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have hR : D.residual q =
      CSParisiMeasure.variationalValue (physicalResidualMixture μ q hq) β :=
    tendsto_nhds_unique (D.residual_limit q hq) (hChen _ β hβ.le)
  set V := CSStructure.potential μ β (twoAtom x Q) q
  set M := curvature β (twoAtom x Q) q
  have hV : 0 < V := h.positive_off_contact q hq hqQ
  have hM : 0 < M := ground_trial_curvature_pos μ h hq
  have hε : 0 ≤ V / (2 * β ^ 2 * M) := by positivity
  have hground : D.ground q ≤
      functional μ β (twoAtom x Q) q 0 - V ^ 2 / (8 * β ^ 4 * M) := by
    calc D.ground q ≤ groundFunctional (centerMixture μ q hq.1)
          (trialGroundProfile h hq hε) := center_ground_le_profile hChen D hq _
      _ = functional μ β (twoAtom x Q) q (V / (2 * β ^ 2 * M)) :=
          groundFunctional_trialGroundProfile h hq hε
      _ ≤ functional μ β (twoAtom x Q) q 0 - V ^ 2 / (8 * β ^ 4 * M) :=
          ground_trial_strict_contact_gap μ h hq hqQ
  have hres : D.residual q ≤
      (residualTrial h.weight_range h.overlap_range hq).value β
        (residualMixture μ hq).xi := by
    rw [hR]
    exact CSParisiMeasure.canonicalMinimizer_isMinimizer (residualMixture μ hq) β _
  have htel := telescope h hq
  have hβg := mul_le_mul_of_nonneg_left hground hβ.le
  have hscale : β * (V ^ 2 / (8 * β ^ 4 * M)) = V ^ 2 / (8 * β ^ 3 * M) := by
    field_simp [hβ.ne', hM.ne']
  unfold tapValue
  rw [hP, htel]
  nlinarith [hβg, hres, hscale]

/-- Strict TAP exclusion away from the certificate contact, with Chen
as its sole literature hypothesis. -/
theorem strictTAPGap_reduced3 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (D : ThermodynamicData μ β) :
    ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q → tapValue D q < D.pressure := by
  intro q hq hqQ
  have hgap := tapValue_le_pressure_sub_gap_reduced3 hChen h D hq hqQ
  have hV : 0 < CSStructure.potential μ β (twoAtom x Q) q :=
    h.positive_off_contact q hq hqQ
  have hM : 0 < curvature β (twoAtom x Q) q := ground_trial_curvature_pos μ h hq
  have hpos : 0 < (CSStructure.potential μ β (twoAtom x Q) q) ^ 2 /
      (8 * β ^ 3 * curvature β (twoAtom x Q) q) := by
    have := h.beta_pos
    positivity
  linarith

end SlowEquilibration.LiteratureSubagBandUpperExtraction

namespace SlowEquilibration.LiteratureSubagBandUpperExtraction.Endpoints

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate LiteratureSubagTAP
open LiteratureSubagPhysicalDefinitions LiteratureSubagRemark25Proof
open LiteratureSubagRemark25Final LiteratureSubagTheorem5Proof
open SourceLiteratureParisi LiteratureSubagReplicaExclusion
open scoped Topology

set_option autoImplicit false

/-- Exponential replica exclusion uses Chen and the remaining upper
band approximation, without extraction, Theorem 5, Remark 25, or Chen--Sen. -/
theorem exponential_replica_exclusion_reduced3
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hupper : ExpectedBandUpperApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le))
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≠ Q) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  let D := chenThermodynamicData hChen μ h.beta_pos.le
  exact exponential_exclusion_of_strictTAPGap_reduced2 D h.beta_pos hupper
    (subsequenceBandExtraction D) hq
    (strictTAPGap_reduced3 hChen h D q hq hqQ)

/-- The directing norm has the same remaining upper-band input; the
ground trial bound removes Chen--Sen from this endpoint as well. -/
theorem physicalDirectingNormQ_of_literature_reduced3
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hupper : ExpectedBandUpperApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    PureCapturePhysicalCoarseDiniAssembly.PhysicalDirectingNormQ μ β Q := by
  apply SourcePureCapturePhysicalNormParisiExclusion.physical_directing_normQ_of_parisi_and_replica_exclusion μ h
    (SourceLiteratureParisiTemperatureEven.finite_pressure_limit_all_real_shift hChen μ)
  intro q hq hqQ
  obtain ⟨k, _hk, ρ, hρ, c, hc, hb⟩ :=
    exponential_replica_exclusion_reduced3 hChen h hupper hq hqQ
  exact ⟨k, ρ, hρ,
    LiteratureSubagFullOverlapAdapter.fullOverlapLaw_equilateral_tendsto_zero_of_expected
      μ β q ρ k (expectedOverlapBlockProbability_tendsto_zero_of_exponential
        μ β q ρ c k hc hb)⟩

/-- The full Remark 25 interface after discharging extraction. The upper
and lower band approximations and block reconstruction remain explicit;
the reduction uses neither Theorem 5 nor a ground variational hypothesis. -/
theorem remark25Contrapositive_reduced3
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation D)
    (hlower : ExpectedBandLowerApproximation D)
    (hcompare : BandBlockRateComparison μ β) : Remark25Contrapositive μ β :=
  LiteratureSubagTheorem5Proof.remark25Contrapositive_of_band_estimates_reduced2
    D hβ hupper hlower (subsequenceBandExtraction D) hcompare

end SlowEquilibration.LiteratureSubagBandUpperExtraction.Endpoints
