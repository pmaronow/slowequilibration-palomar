-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerLatitude
public import SlowEquilibration.LiteratureSubagBandLowerComplete
public import SlowEquilibration.LiteratureSubagBandLowerResidual
public import SlowEquilibration.SphericalLatitudeFrameParseval

/-!
Subag's expected thick-latitude lower comparison with the original replica
and tolerance quantifiers. Replicated coarea retains the whole transverse
block, and the continuous-field law transports its restricted log partition
at the corrected temperature. Orthogonal Gaussian projection removes the
Taylor linear term in expectation.

A random tensor derivative envelope controls latitude thickening for every
disorder realization and has a dimension-independent mean. Thus this
comparison needs neither pressure lower tails nor a restriction to regular
disorder. Positivity and finite Gaussian log-partition integrability are
proved before taking logarithms and expectations. The separate residual
replicated limit remains explicit only in the final composition lemma.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagThickLatitudeLower

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof LiteratureSubagBandLowerProof LiteratureSubagTheorem10Proof
open LiteratureSubagBandLowerComplete LiteratureSubagBandLowerLatitude
open SphericalTaylorRemainder SphericalGaussianJet WholeFieldRegression
open SphericalPairCommonFrame SphericalTwoPointCovariance
open scoped Topology BigOperators ENNReal RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A restricted replicated log partition is a Borel observable of the
entire continuous field. The restriction need not have full mass. -/
private theorem replicatedLogPartition_measurable
    {K V : Type*} [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {k : ℕ} (ν : Measure V) [SFinite ν] (β : ℝ)
    (a : Fin k → V → K) (ha : ∀ i, Continuous (a i)) :
    Measurable (fun f : C(K, ℝ) =>
      Real.log (∫ v, Real.exp (β * ∑ i : Fin k, f (a i v)) ∂ν)) := by
  have hj : Continuous (fun p : C(K, ℝ) × V =>
      Real.exp (β * ∑ i : Fin k, p.1 (a i p.2))) := by
    apply Real.continuous_exp.comp
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    exact continuous_eval.comp (continuous_fst.prodMk ((ha i).comp continuous_snd))
  exact hj.measurable.stronglyMeasurable.integral_prod_right.measurable.log

/-- The transverse residual law survives an arbitrary finite replica
restriction, and uses the physical temperature `β * sqrt (N / d)`. -/
private theorem restricted_replicatedTaylor_logPartition_law
    {K V : Type*} [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {N d k : ℕ} (hN : 0 < N) (hd : 0 < d)
    (ν : Measure V) [SFinite ν] (β : ℝ) (μ : FiniteMixture)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ y, inner ℝ (e y) u = 0)
    (x : K → Vector d) (hx : Continuous x)
    (a : Fin k → V → K) (ha : ∀ i, Continuous (a i)) :
    (disorderLaw N μ.maxDegree).map (fun J => Real.log (∫ v,
      Real.exp (β * ∑ i : Fin k,
        taylorRemainderCLM (centerCoefficients (mixtureCoefficients μ) q) u
          (transverseOffset e q (x (a i v))) (euclideanDisorder J)) ∂ν)) =
    (disorderLaw d (physicalResidualMixture μ q hq).maxDegree).map
      (fun J => Real.log (∫ v,
        Real.exp ((β * Real.sqrt ((N : ℝ) / (d : ℝ))) * ∑ i : Fin k,
          field (mixtureCoefficients (physicalResidualMixture μ q hq)) J
            (x (a i v))) ∂ν)) := by
  let c := centerCoefficients (mixtureCoefficients μ) q
  let θ := physicalResidualMixture μ q hq
  let z := fun w => transverseOffset e q (x w)
  have hz : Continuous z := transverseOffset_parameter_continuous e q x hx
  let X := fun J => taylorContinuousField c u z hz (euclideanDisorder J)
  let Y := fun J : Disorder d θ.maxDegree => Real.sqrt ((N : ℝ) / (d : ℝ)) •
    modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)
  have hX : Measurable X := (taylorContinuousField c u z hz).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  have hY : Measurable Y :=
    ((modelContinuousField (mixtureCoefficients θ) x hx).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)).const_smul (Real.sqrt ((N : ℝ) / (d : ℝ)))
  have hLaw := transverse_taylorContinuousField_law hN hd μ hq u hu e he x hx
  change (disorderLaw N μ.maxDegree).map X = (disorderLaw d θ.maxDegree).map Y at hLaw
  have hp := ContinuousFieldLaw.observable_map_eq _ _ X Y hX hY hLaw
    (fun f => Real.log (∫ v, Real.exp (β * ∑ i : Fin k, f (a i v)) ∂ν))
    (replicatedLogPartition_measurable ν β a ha)
  convert hp using 1
  · rfl
  · congr 1
    funext J
    congr 1
    apply integral_congr_ae
    exact .of_forall fun v => by
      simp only [Y, ContinuousMap.smul_apply, smul_eq_mul,
        modelContinuousField_apply, valueObservation_actual, ← Finset.mul_sum]
      congr 1
      ring

/-- Equality of the corresponding restricted expectations, without an
annealed replacement or a logarithmic floor. -/
private theorem expected_restricted_replicatedTaylor_logPartition_eq
    {K V : Type*} [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {N d k : ℕ} (hN : 0 < N) (hd : 0 < d)
    (ν : Measure V) [SFinite ν] (β : ℝ) (μ : FiniteMixture)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ y, inner ℝ (e y) u = 0)
    (x : K → Vector d) (hx : Continuous x)
    (a : Fin k → V → K) (ha : ∀ i, Continuous (a i)) :
    (∫ J, Real.log (∫ v, Real.exp (β * ∑ i : Fin k,
      taylorRemainderCLM (centerCoefficients (mixtureCoefficients μ) q) u
        (transverseOffset e q (x (a i v))) (euclideanDisorder J)) ∂ν)
      ∂disorderLaw N μ.maxDegree) =
    ∫ J, Real.log (∫ v,
      Real.exp ((β * Real.sqrt ((N : ℝ) / (d : ℝ))) * ∑ i : Fin k,
        field (mixtureCoefficients (physicalResidualMixture μ q hq)) J
          (x (a i v))) ∂ν)
      ∂disorderLaw d (physicalResidualMixture μ q hq).maxDegree := by
  let c := centerCoefficients (mixtureCoefficients μ) q
  let θ := physicalResidualMixture μ q hq
  let z := fun w => transverseOffset e q (x w)
  have hz : Continuous z := transverseOffset_parameter_continuous e q x hx
  let F := fun f : C(K, ℝ) =>
    Real.log (∫ v, Real.exp (β * ∑ i : Fin k, f (a i v)) ∂ν)
  have hF := replicatedLogPartition_measurable ν β a ha
  let X := fun J => taylorContinuousField c u z hz (euclideanDisorder J)
  let Y := fun J : Disorder d θ.maxDegree => Real.sqrt ((N : ℝ) / (d : ℝ)) •
    modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)
  have hX : Measurable X := (taylorContinuousField c u z hz).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  have hY : Measurable Y :=
    ((modelContinuousField (mixtureCoefficients θ) x hx).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)).const_smul (Real.sqrt ((N : ℝ) / (d : ℝ)))
  have hLaw := transverse_taylorContinuousField_law hN hd μ hq u hu e he x hx
  change (disorderLaw N μ.maxDegree).map X = (disorderLaw d θ.maxDegree).map Y at hLaw
  have hmean : (∫ J, F (X J) ∂disorderLaw N μ.maxDegree) =
      ∫ J, F (Y J) ∂disorderLaw d θ.maxDegree := by
    rw [← integral_map hX.aemeasurable hF.aestronglyMeasurable,
      ← integral_map hY.aemeasurable hF.aestronglyMeasurable, hLaw]
  convert hmean using 1
  · rfl
  · congr 1
    funext J
    congr 1
    apply integral_congr_ae
    exact .of_forall fun v => by
      simp only [Y, ContinuousMap.smul_apply, smul_eq_mul,
        modelContinuousField_apply, valueObservation_actual, ← Finset.mul_sum]
      congr 1
      ring


private theorem latitudeMap_centered_offset {n : ℕ} (hn : 1 ≤ n)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (u : Vector (n + 1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (x : Vector n) :
    Real.sqrt q • (u + transverseOffset e q x) =
      latitudeMap u e (Real.sqrt q) x := by
  have hq0 : 0 < q := hq.1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : Real.sqrt q *
      Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q) / (q * (n : ℝ))) =
      Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ) * (1 - q)) := by
    rw [← Real.sqrt_mul hq0.le]
    congr 1
    field_simp
  rw [smul_add, transverseOffset, smul_smul, hs, latitudeMap,
    Real.sq_sqrt hq0.le]

/-- Removing the Taylor linear term and transporting the restricted law
bounds the actual central slice below by the corrected residual model.
The measure can be the full transverse overlap-block restriction. -/
private theorem expected_centralLatitude_logPartition_lower
    {V : Type*} [TopologicalSpace V] [CompactSpace V]
    [SecondCountableTopology V] [T2Space V] [Nonempty V]
    [MeasurableSpace V] [BorelSpace V]
    {n k : ℕ} (hn : 1 ≤ n) (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (μ : FiniteMixture) (β : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ y, inner ℝ (e y) u = 0)
    (x : Fin k → V → Vector n) (hx : ∀ i, Continuous (x i)) :
    (∫ J, Real.log (∫ v,
      Real.exp ((β * Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ))) * ∑ i : Fin k,
        field (mixtureCoefficients (physicalResidualMixture μ q hq)) J (x i v)) ∂ν)
      ∂disorderLaw n (physicalResidualMixture μ q hq).maxDegree) ≤
    ∫ J, Real.log (∫ v, Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (x i v)) -
        field (mixtureCoefficients μ) J (Real.sqrt q • u))) ∂ν)
      ∂disorderLaw (n + 1) μ.maxDegree := by
  by_cases hk : k = 0
  · subst k
    simp only [Fin.sum_univ_zero, mul_zero, Real.exp_zero, integral_const,
      probReal_univ, one_smul, le_refl]
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  let : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  let y : Fin k × V → Vector n := fun w => x w.1 w.2
  have hy : Continuous y := continuous_prod_of_discrete_left.mpr hx
  let a : Fin k → V → Fin k × V := fun i v => (i, v)
  have ha : ∀ i, Continuous (a i) := fun _ => continuous_const.prodMk continuous_id
  have hLaw := expected_restricted_replicatedTaylor_logPartition_eq
    (by omega : 0 < n + 1) (by omega : 0 < n) ν β μ hq u hu e he y hy a ha
  let c := centerCoefficients (mixtureCoefficients μ) q
  let z : Fin k → V → Vector (n + 1) :=
    fun i v => transverseOffset e q (x i v)
  have hz : ∀ i, Continuous (z i) := fun i =>
    transverseOffset_parameter_continuous e q (x i) (hx i)
  have ht : ∀ i v, inner ℝ (z i v) u = 0 := fun i v =>
    transverseOffset_tangent u e he q (x i v)
  have hrem := expected_replicatedTaylor_logPartition_le
    (by omega : 0 < n + 1) ν c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hq.1.le)
    β u z hz ht
  have hright (J : Disorder (n + 1) μ.maxDegree) (v : V) (i : Fin k) :
      field c J (u + z i v) - field c J u =
        field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (x i v)) -
          field (mixtureCoefficients μ) J (Real.sqrt q • u) := by
    dsimp only [c, z]
    rw [field_center_scale _ (mixtureCoefficients_nonnegative μ) hq.1.le,
      field_center_scale _ (mixtureCoefficients_nonnegative μ) hq.1.le,
      latitudeMap_centered_offset hn hq]
  simp_rw [hright] at hrem
  exact hLaw ▸ hrem

private theorem overlapBlock_measurable {N k : ℕ} (q θ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q θ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

/-- Compact replica coordinates transport even a restricted integral
exactly to the original product spherical measure. -/
private theorem replicated_compactSphere_integral {n k : ℕ} (hn : 1 ≤ n)
    {A : Set (Fin k → Vector n)} (hA : MeasurableSet A)
    (f : (Fin k → Vector n) → ℝ) (hf : Measurable f) :
    (∫ y in {y : Fin k → CompactSphereCarrier.Carrier n |
        (fun i => (y i : Vector n)) ∈ A}, f (fun i => (y i : Vector n))
      ∂Measure.pi (fun _ : Fin k => CompactSphereCarrier.law n)) =
      ∫ y in A, f y ∂Measure.pi (fun _ : Fin k => sphereLaw n) := by
  let := CompactSphereCarrier.law_probability hn
  let T : (Fin k → CompactSphereCarrier.Carrier n) → Fin k → Vector n :=
    fun y i => (y i : Vector n)
  have hT : Measurable T := .of_eval fun i =>
    measurable_subtype_coe.comp (measurable_pi_apply i)
  have hm : (Measure.pi (fun _ : Fin k => CompactSphereCarrier.law n)).map T =
      Measure.pi (fun _ : Fin k => sphereLaw n) := by
    dsimp only [T]
    rw [Measure.pi_map_pi (fun _ : Fin k => measurable_subtype_coe.aemeasurable)]
    simp_rw [CompactSphereCarrier.law_map_coe hn]
  change (∫ y in T ⁻¹' A, f (T y) ∂Measure.pi (fun _ : Fin k => CompactSphereCarrier.law n)) = _
  rw [← integral_indicator (hA.preimage hT), ← integral_indicator hA, ← hm,
    integral_map hT.aemeasurable (hf.indicator hA).aestronglyMeasurable]
  rfl

/-- The unnormalized central slice partition, with its entire transverse
zero-overlap block retained. -/
private def centralLatitudePartition {n : ℕ} (k : ℕ) (μ : FiniteMixture) (β q θ : ℝ)
    (u : Vector (n + 1)) (e : Vector n →ₗᵢ[ℝ] Vector (n + 1))
    (J : Disorder (n + 1) μ.maxDegree) : ℝ :=
  ∫ y in overlapBlock 0 θ, Real.exp (β * ∑ i : Fin k,
    (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
      field (mixtureCoefficients μ) J (Real.sqrt q • u)))
    ∂Measure.pi (fun _ : Fin k => sphereLaw n)


private theorem latitudeFrameAt_apply_adjoint {n : ℕ}
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (v : Vector (n + 1)) (ht : inner ℝ v u = 0) :
    latitudeFrameAt u ((latitudeFrameAt u).toContinuousLinearMap.adjoint v) = v := by
  let e := latitudeFrameAt u
  have hn : ‖e.toContinuousLinearMap.adjoint v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := latitudeFrameAt_adjoint_inner u hu v v
    simpa only [real_inner_self_eq_norm_sq, ht, zero_mul, zero_div, sub_zero] using h
  have hi : inner ℝ (e (e.toContinuousLinearMap.adjoint v)) v =
      ‖e.toContinuousLinearMap.adjoint v‖ ^ 2 := by
    calc
      _ = inner ℝ (e.toContinuousLinearMap.adjoint v)
          (e.toContinuousLinearMap.adjoint v) :=
        (e.toContinuousLinearMap.adjoint_inner_right _ _).symm
      _ = _ := real_inner_self_eq_norm_sq _
  have hz : ‖e (e.toContinuousLinearMap.adjoint v) - v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, e.norm_map, hi, hn]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

private theorem latitude_reconstruction {n : ℕ} (hn : 1 ≤ n)
    (u σ : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (hσ : ‖σ‖ ^ 2 = ((n + 1 : ℕ) : ℝ)) (hr : |overlap u σ| < 1) :
    let y := Real.sqrt (n : ℝ) • (latitudeFrameAt u).toContinuousLinearMap.adjoint
      (planeDirection u σ)
    ‖y‖ ^ 2 = (n : ℝ) ∧ latitudeMap u (latitudeFrameAt u) (overlap u σ) y = σ := by
  let e := latitudeFrameAt u
  let d := planeDirection u σ
  let r := overlap u σ
  let y := Real.sqrt (n : ℝ) • e.toContinuousLinearMap.adjoint d
  have hdim : 0 < n + 1 := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have ht : inner ℝ d u = 0 := planeDirection_tangent hdim u σ hu
  have hd : ‖d‖ = 1 := planeDirection_norm hdim u σ hu hσ hr
  have hadj : ‖e.toContinuousLinearMap.adjoint d‖ ^ 2 = 1 := by
    have h := latitudeFrameAt_adjoint_inner u hu d d
    simpa only [real_inner_self_eq_norm_sq, ht, zero_mul, zero_div, sub_zero,
      hd, one_pow] using h
  have hy : ‖y‖ ^ 2 = (n : ℝ) := by
    dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hnR.le, hadj, mul_one]
  have harg : 0 ≤ 1 - r ^ 2 := by
    have h := abs_le.mp hr.le
    dsimp only [r]
    nlinarith
  have hc : Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ) * (1 - r ^ 2)) *
      Real.sqrt (n : ℝ) = planeScale u σ := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnR.le,
      Real.sq_sqrt (by positivity)]
    dsimp only [r]
    field_simp
  have he : e (e.toContinuousLinearMap.adjoint d) = d :=
    latitudeFrameAt_apply_adjoint u hu d ht
  have hrec : planeScale u σ • d = σ - r • u := by
    dsimp only [d, planeDirection]
    rw [smul_smul, mul_inv_cancel₀ (planeScale_pos hdim u σ hr).ne', one_smul]
  refine ⟨hy, ?_⟩
  change r • u + Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ) * (1 - r ^ 2)) • e y = σ
  dsimp only [y]
  rw [map_smul, he, smul_smul, hc, hrec, add_sub_cancel]

private def derivativeEnvelope {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) *
    SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)

private theorem derivativeEnvelope_nonneg {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : 0 ≤ derivativeEnvelope c J := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (by positivity)
    (SphericalAging.GaussianLandscape.landscapeNorm_nonnegative _ _ _)

private theorem field_fderiv_le_envelope {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N)
    (hx : x ∈ Metric.closedBall 0 (Real.sqrt (N : ℝ))) :
    ‖fderiv ℝ (field c J) x‖ ≤ derivativeEnvelope c J * Real.sqrt (N : ℝ) := by
  have hball : ‖x‖ ≤ Real.sqrt (N : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hjet := field_iteratedFDeriv_ball_bound hN c J x hball 1
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  simp only [pow_one, norm_iteratedFDeriv_one, Nat.descFactorial_one] at hjet
  apply (mul_le_mul_iff_right₀ hs).mp
  calc
    _ ≤ (N : ℝ) * derivativeEnvelope c J := hjet
    _ = _ := by
      calc
        _ = derivativeEnvelope c J * Real.sqrt (N : ℝ) ^ 2 := by rw [hsq]; ring
        _ = _ := by ring

private def derivativeMean {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) *
    SphericalAging.GaussianLandscapeMoments.momentCeiling p.val.val 1

private theorem degree_landscape_integrable_mean {N P : ℕ}
    (hN : 1 ≤ N) (p : Degree P) :
    Integrable (fun J : Disorder N P =>
      SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)) (disorderLaw N P) ∧
    (∫ J : Disorder N P,
      SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) ∂disorderLaw N P) ≤
      SphericalAging.GaussianLandscapeMoments.momentCeiling p.val.val 1 := by
  have hb := SphericalAging.GaussianLandscapeMoments.uniform_real_power_moment hN
    (show 0 < p.val.val by omega) (k := 1) (by norm_num)
  simp only [Real.rpow_one] at hb
  refine ⟨(degree_block_hasLaw p).integrable_comp hb.1, ?_⟩
  have heq := (degree_block_hasLaw (N := N) p).integral_comp hb.1.aestronglyMeasurable
  have heq' : (∫ J : Disorder N P,
      SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) ∂disorderLaw N P) =
      ∫ J : SphericalAging.FiniteModel.Disorder N p.val.val,
        SphericalAging.GaussianLandscape.landscapeNorm N p.val.val J
          ∂SphericalAging.FiniteModel.disorderLaw N p.val.val := by
    simpa only [Function.comp_def] using heq
  rw [heq']
  exact hb.2

private theorem derivativeEnvelope_integrable {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    Integrable (derivativeEnvelope (N := N) c) (disorderLaw N P) := by
  apply integrable_finsetSum
  intro p _
  exact (degree_landscape_integrable_mean hN p).1.const_mul _

private theorem expected_derivativeEnvelope_le {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    (∫ J : Disorder N P, derivativeEnvelope c J ∂disorderLaw N P) ≤ derivativeMean c := by
  unfold derivativeEnvelope derivativeMean
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    exact Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (degree_landscape_integrable_mean hN p).2 (by positivity)
  · intro p _
    exact (degree_landscape_integrable_mean hN p).1.const_mul _


private theorem normalized_frame_inner {n : ℕ}
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (x y : Vector n) :
    inner ℝ ((Real.sqrt (n : ℝ))⁻¹ • e x) ((Real.sqrt (n : ℝ))⁻¹ • e y) =
      overlap x y := by
  rw [real_inner_smul_left, real_inner_smul_right, e.inner_map_map,
    ← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact mul_comm _ _

private theorem centralLatitude_direction {n : ℕ} (hn : 1 ≤ n)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (u : Vector (n + 1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (y : Vector n) :
    Real.sqrt q • u + Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) •
        ((Real.sqrt (n : ℝ))⁻¹ • e y) = latitudeMap u e (Real.sqrt q) y := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hq1 : 0 ≤ 1 - q := sub_nonneg.mpr hq.2.le
  have hc : Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) * (Real.sqrt (n : ℝ))⁻¹ =
      Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ) * (1 - q)) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hn0.le, Real.sq_sqrt (by positivity)]
    field_simp
  rw [smul_smul, hc, latitudeMap, Real.sq_sqrt hq.1.le]

private def angularLatitudeWeight {n : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q θ : ℝ) (u : Vector (n + 1)) (J : Disorder (n + 1) μ.maxDegree)
    (ω : Fin k → Vector (n + 1)) : ℝ :=
  {v : Fin k → Vector (n + 1) | ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| < θ}.indicator
    (fun v => Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J
        (Real.sqrt q • u + Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) • v i) -
        field (mixtureCoefficients μ) J (Real.sqrt q • u)))) ω

private theorem angularLatitudeWeight_measurable {n k : ℕ} (μ : FiniteMixture)
    (β q θ : ℝ) (u : Vector (n + 1)) (J : Disorder (n + 1) μ.maxDegree) :
    Measurable (angularLatitudeWeight k μ β q θ u J) := by
  apply Measurable.indicator
  · apply Continuous.measurable
    exact Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ =>
      ((field_contDiff _ J).continuous.comp
        (continuous_const.add ((continuous_apply i).const_smul (Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)))))).sub
          continuous_const).const_mul β)
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- Replicated coarea retains the entire transverse block and the exact
`k`th power of the actual latitude-window mass. -/
private theorem replicated_latitude_direction_integral {n k : ℕ} (hn : 2 ≤ n)
    (μ : FiniteMixture) (β : ℝ) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (θ η : ℝ)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (J : Disorder (n + 1) μ.maxDegree) :
    (∫ σ in univ.pi (fun _ : Fin k => overlapRegion u {r | |r - Real.sqrt q| ≤ η}),
      angularLatitudeWeight k μ β q θ u J (fun i => planeDirection u (σ i))
        ∂Measure.pi (fun _ : Fin k => sphereLaw (n + 1))) =
      ((sphereLaw (n + 1)).real (overlapRegion u {r | |r - Real.sqrt q| ≤ η})) ^ k *
        centralLatitudePartition k μ β q θ u (latitudeFrameAt u) J := by
  have hA : MeasurableSet {r : ℝ | |r - Real.sqrt q| ≤ η} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rw [replicatedRestrictedSphere_direction_integral hn u hu hA _
    (angularLatitudeWeight_measurable μ β q θ u J)]
  congr 1
  unfold centralLatitudePartition
  rw [← integral_indicator (overlapBlock_measurable (N := n) (k := k) 0 θ)]
  apply integral_congr_ae
  exact .of_forall fun y => by
    have hpair : (∀ i j : Fin k, i ≠ j →
        |inner ℝ ((Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u (y i))
          ((Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u (y j))| < θ) ↔
        y ∈ overlapBlock 0 θ := by
      simp only [normalized_frame_inner, overlapBlock, mem_ofPred_eq, sub_zero]
    unfold angularLatitudeWeight
    by_cases hy : y ∈ overlapBlock 0 θ
    · simp only [Set.indicator, mem_ofPred_eq, hpair, hy, ↓reduceIte]
      simp_rw [centralLatitude_direction (by omega : 1 ≤ n) hq]
    · simp only [Set.indicator, mem_ofPred_eq, hpair, hy, ↓reduceIte]

private theorem replicated_integrand_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    Integrable (fun σ : Fin k → Vector N => Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m)))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) := by
  have hi : Integrable (fun x : Vector N =>
      Real.exp (β * (field (mixtureCoefficients μ) J x - field (mixtureCoefficients μ) J m)))
      (sphereLaw N) := partition_integrand_integrable hN β
        ((field_contDiff _ J).continuous.sub continuous_const)
  convert Integrable.fintype_prod (fun _ : Fin k => hi) using 1
  ext σ
  rw [Finset.mul_sum, Real.exp_sum]

private theorem replicatedBand_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i =>
      (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet


/-- Thickening the replicated slice holds for every disorder realization.
The random cost has a dimension-independent expectation. -/
private theorem replicatedBandPartition_lower_of_latitude {n k : ℕ} (hn : 2 ≤ n)
    (μ : FiniteMixture) (β : ℝ) {q δ ρ θ η : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hηa : η < Real.sqrt q) (hη1 : η < 1 - Real.sqrt q)
    (hηδ : η ≤ δ) (hwidth : 2 * η + θ ≤ ρ)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (J : Disorder (n + 1) μ.maxDegree) :
    Real.exp (-(2 * |β| * derivativeEnvelope (mixtureCoefficients μ) J * Real.sqrt η) *
        (((n + 1 : ℕ) : ℝ) * (k : ℝ))) *
      ((sphereLaw (n + 1)).real (overlapRegion u {r | |r - Real.sqrt q| ≤ η})) ^ k *
        centralLatitudePartition k μ β q θ u (latitudeFrameAt u) J ≤
      replicatedBandPartition k μ β q δ ρ J (Real.sqrt q • u) := by
  let m := Real.sqrt q • u
  let S := univ.pi (fun _ : Fin k => overlapRegion u {r | |r - Real.sqrt q| ≤ η})
  let B := ReplicatedBand k q δ ρ m
  let A := {ω : Fin k → Vector (n + 1) | ∀ i j, i ≠ j → |inner ℝ (ω i) (ω j)| < θ}
  let F := fun σ : Fin k → Vector (n + 1) => Real.exp (β * ∑ i : Fin k,
    (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m))
  let E := 2 * |β| * derivativeEnvelope (mixtureCoefficients μ) J * Real.sqrt η
  let C := Real.exp (-E * (((n + 1 : ℕ) : ℝ) * (k : ℝ)))
  have hB : MeasurableSet B := replicatedBand_measurable q δ ρ m
  have hS : MeasurableSet S := MeasurableSet.pi (Set.to_countable univ) fun _ _ =>
    overlapRegion_measurable u ((isClosed_le (by fun_prop) continuous_const).measurableSet)
  have hiF := replicated_integrand_integrable (k := k) (by omega : 1 ≤ n + 1) μ β J m
  have hco := replicated_latitude_direction_integral (k := k) hn μ β hq θ η u hu J
  change C * _ * _ ≤ ∫ σ in B, F σ ∂Measure.pi (fun _ : Fin k => sphereLaw (n + 1))
  rw [mul_assoc, ← hco, ← integral_indicator hS, ← integral_const_mul,
    ← integral_indicator hB]
  apply integral_mono_of_nonneg
    (.of_forall fun σ => mul_nonneg (Real.exp_nonneg _)
      (indicator_nonneg (fun _ _ => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _) _))
    (hiF.indicator hB)
  let : IsProbabilityMeasure (sphereLaw (n + 1)) := sphereLaw_probability (n + 1)
  have hsupp : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw (n + 1)),
      ∀ i : Fin k, ‖σ i‖ ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    eventually_all.mpr fun i => (@Measure.tendsto_eval_ae_ae
      (Fin k) (fun _ => Vector (n + 1)) inferInstance
      (fun _ => inferInstance) (fun _ => sphereLaw (n + 1))
      (fun _ => inferInstance) i).eventually
        (sphereLaw_support (by omega : 1 ≤ n + 1))
  filter_upwards [hsupp] with σ hσ
  by_cases hSσ : σ ∈ S
  · rw [indicator_of_mem hSσ]
    by_cases hAσ : (fun i => planeDirection u (σ i)) ∈ A
    · let r := fun i => overlap u (σ i)
      have hnear (i : Fin k) : |r i - Real.sqrt q| ≤ η := by
        have h := hSσ i (mem_univ i)
        change |overlap (σ i) u - Real.sqrt q| ≤ η at h
        simpa only [r, overlap, real_inner_comm] using h
      have hr (i : Fin k) : |r i| < 1 := by
        have hb := abs_le.mp (hnear i)
        have hs := Real.sqrt_nonneg q
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      let e := latitudeFrameAt u
      let y := fun i => Real.sqrt (n : ℝ) • e.toContinuousLinearMap.adjoint
        (planeDirection u (σ i))
      have hy (i : Fin k) : ‖y i‖ ^ 2 = (n : ℝ) :=
        (latitude_reconstruction (by omega : 1 ≤ n) u (σ i) hu (hσ i) (hr i)).1
      have hrec (i : Fin k) : latitudeMap u e (r i) (y i) = σ i :=
        (latitude_reconstruction (by omega : 1 ≤ n) u (σ i) hu (hσ i) (hr i)).2
      have hd (i : Fin k) : (Real.sqrt (n : ℝ))⁻¹ • e (y i) = planeDirection u (σ i) := by
        dsimp only [y]
        rw [map_smul, latitudeFrameAt_apply_adjoint u hu _
          (planeDirection_tangent (by omega : 0 < n + 1) u (σ i) hu),
          smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr
            (Nat.cast_pos.mpr (by omega : 0 < n))).ne', one_smul]
      have hpair : ∀ i j : Fin k, i ≠ j → |overlap (y i) (y j)| < θ := by
        intro i j hij
        rw [← normalized_frame_inner e, hd, hd]
        exact hAσ i j hij
      have hmem : σ ∈ B := by
        have hm' := LiteratureSubagBandLowerFinal.variableLatitude_mem_replicatedBand
          (by omega : 1 ≤ n) hq hηδ hwidth u hu e (latitudeFrameAt_orthogonal u hu)
          r (fun i => (hr i).le) hnear y hpair
        simpa only [hrec] using hm'
      rw [indicator_of_mem hmem]
      change C * angularLatitudeWeight k μ β q θ u J
        (fun i => planeDirection u (σ i)) ≤ F σ
      rw [angularLatitudeWeight, indicator_of_mem hAσ, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : |Real.sqrt q| ≤ 1 := by
        rw [abs_of_nonneg (Real.sqrt_nonneg q)]
        exact Real.sqrt_le_one.mpr hq.2.le
      have hball (s : ℝ) (hs : |s| ≤ 1) (i : Fin k) :
          latitudeMap u e s (y i) ∈ Metric.closedBall 0 (Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
        rw [Metric.mem_closedBall, dist_zero_right,
          ← latitudeMap_norm_sq (by omega : 1 ≤ n) u hu e
            (latitudeFrameAt_orthogonal u hu) hs (y i) (hy i), Real.sqrt_sq (norm_nonneg _)]
      have hvar (i : Fin k) :
          |field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
            field (mixtureCoefficients μ) J (σ i)| ≤
            2 * derivativeEnvelope (mixtureCoefficients μ) J *
              ((n + 1 : ℕ) : ℝ) * Real.sqrt η := by
        have hf := (convex_closedBall (0 : Vector (n + 1))
          (Real.sqrt ((n + 1 : ℕ) : ℝ))).norm_image_sub_le_of_norm_fderiv_le
            (fun x _ => (field_contDiff (mixtureCoefficients μ) J).differentiable (by simp) x)
            (field_fderiv_le_envelope (by omega : 1 ≤ n + 1) (mixtureCoefficients μ) J)
            (hball (r i) (hr i).le i) (hball (Real.sqrt q) ha i)
        have hdist := latitudeMap_dist_le (by omega : 1 ≤ n) u hu e
          (latitudeFrameAt_orthogonal u hu) ha (hr i).le (y i) (hy i)
        rw [hrec] at hf hdist
        have hh := hf.trans (mul_le_mul_of_nonneg_left hdist
          (mul_nonneg (derivativeEnvelope_nonneg _ _) (Real.sqrt_nonneg _)))
        rw [abs_sub_comm] at hh
        have hs := Real.sqrt_le_sqrt (hnear i)
        calc
          _ ≤ _ := hh
          _ ≤ (derivativeEnvelope (mixtureCoefficients μ) J * Real.sqrt ((n + 1 : ℕ) : ℝ)) *
              (2 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt η) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hs (by positivity))
              (mul_nonneg (derivativeEnvelope_nonneg _ _) (Real.sqrt_nonneg _))
          _ = _ := by
            rw [show (derivativeEnvelope (mixtureCoefficients μ) J * Real.sqrt ((n + 1 : ℕ) : ℝ)) *
              (2 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt η) =
              2 * derivativeEnvelope (mixtureCoefficients μ) J *
                Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt η by ring,
              Real.sq_sqrt (Nat.cast_nonneg (n + 1))]
      have hsum := Finset.abs_sum_le_sum_abs
        (fun i : Fin k => field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
          field (mixtureCoefficients μ) J (σ i)) Finset.univ
      have hv : |β * ∑ i : Fin k,
          (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
            field (mixtureCoefficients μ) J (σ i))| ≤
          E * (((n + 1 : ℕ) : ℝ) * (k : ℝ)) := by
        rw [abs_mul]
        calc
          _ ≤ |β| * ∑ i : Fin k,
              |field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
                field (mixtureCoefficients μ) J (σ i)| :=
            mul_le_mul_of_nonneg_left hsum (abs_nonneg β)
          _ ≤ |β| * ∑ _i : Fin k,
              2 * derivativeEnvelope (mixtureCoefficients μ) J *
                ((n + 1 : ℕ) : ℝ) * Real.sqrt η := by gcongr with i; exact hvar i
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, E]; ring
      have hc (i : Fin k) : Real.sqrt q • u +
          Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - q)) • planeDirection u (σ i) =
          latitudeMap u e (Real.sqrt q) (y i) := by
        rw [← hd, centralLatitude_direction (by omega : 1 ≤ n) hq]
      simp_rw [hc]
      dsimp only [C, F, m]
      simp only [Finset.sum_sub_distrib] at hv ⊢
      linarith [le_abs_self (β *
        (∑ i : Fin k, field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
          ∑ i : Fin k, field (mixtureCoefficients μ) J (σ i)))]
    · change C * angularLatitudeWeight k μ β q θ u J
        (fun i => planeDirection u (σ i)) ≤ _
      rw [angularLatitudeWeight, indicator_of_notMem hAσ, mul_zero]
      exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  · rw [indicator_of_notMem hSσ, mul_zero]
    exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _


private theorem field_zero {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) :
    field c J 0 = 0 := by
  unfold field
  apply Finset.sum_eq_zero
  intro p _
  have hp : p.val.val ≠ 0 := by have := p.property; omega
  simp [blockField, SphericalAging.FiniteModel.Hamiltonian,
    SphericalAging.FiniteModel.tensorMonomial, hp]

private theorem zero_overlapBlock_volume_positive {n k : ℕ}
    (hnk : k + 1 ≤ n) (hk : 1 ≤ k) {θ : ℝ} (hθ : 0 < θ) :
    0 < (Measure.pi (fun _ : Fin k => sphereLaw n)) (overlapBlock 0 θ) := by
  let Q : ℝ := min (θ / 2) (1 / 2)
  have hQ : Q ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by positivity) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  obtain ⟨v, hv⟩ := (sphereLaw_support (by omega : 1 ≤ n)).exists
  let m : Vector n := Real.sqrt Q • v
  have hm : ‖m‖ ^ 2 = (n : ℝ) * Q := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hQ.1.le, hv]
    ring
  have hv := SourcePureSection9SmallClosures.replicatedBand_volume_positive hnk hk hQ
    (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < θ / 2) m hm
  apply hv.trans_le (measure_mono ?_)
  intro σ hσ i j hij
  have hb := hσ.2 i j hij
  have ht : |overlap (σ i) (σ j)| ≤ |overlap (σ i) (σ j) - Q| + Q := by
    calc
      _ = |(overlap (σ i) (σ j) - Q) + Q| := by congr 1; ring
      _ ≤ |overlap (σ i) (σ j) - Q| + |Q| := abs_add_le _ _
      _ = _ := by rw [abs_of_pos hQ.1]
  have hQθ : Q ≤ θ / 2 := min_le_left _ _
  change |overlap (σ i) (σ j) - 0| < θ
  rw [sub_zero]
  linarith

private def compactBlockMeasure (n k : ℕ) (θ : ℝ) :
    Measure (Fin k → CompactSphereCarrier.Carrier n) :=
  (Measure.pi (fun _ : Fin k => CompactSphereCarrier.law n)).restrict
    {y | (fun i => (y i : Vector n)) ∈ overlapBlock 0 θ}

private theorem compactBlockMeasure_nonzero {n k : ℕ} (hn : 1 ≤ n)
    {θ : ℝ} (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw n)) (overlapBlock 0 θ)) :
    compactBlockMeasure n k θ ≠ 0 := by
  let := CompactSphereCarrier.law_probability hn
  intro hz
  have hi := replicated_compactSphere_integral hn (overlapBlock_measurable 0 θ)
    (fun _ : Fin k → Vector n => (1 : ℝ)) measurable_const
  change (∫ _, (1 : ℝ) ∂compactBlockMeasure n k θ) = _ at hi
  rw [hz, integral_zero_measure] at hi
  have hpos : 0 < (∫ _y in overlapBlock (N := n) (k := k) 0 θ, (1 : ℝ)
      ∂Measure.pi (fun _ : Fin k => sphereLaw n)) := by
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] using
      (ENNReal.toReal_pos hvol.ne' (measure_ne_top _ _))
  linarith

/-- The expected full central slice dominates exactly the untruncated
residual replicated pressure, normalized per ambient dimension. -/
private theorem residualReplicatedPressure_le_expected_centralLatitude
    {n k : ℕ} (hnk : k + 1 ≤ n) (hk : 1 ≤ k) (μ : FiniteMixture) (β : ℝ)
    {q θ : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hθ : 0 < θ)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ y, inner ℝ (e y) u = 0) :
    residualReplicatedPressure μ β q θ hq k n ≤
      ∫ J, Real.log (centralLatitudePartition k μ β q θ u e J) /
        (((n + 1 : ℕ) : ℝ) * (k : ℝ)) ∂disorderLaw (n + 1) μ.maxDegree := by
  have hn : 1 ≤ n := by omega
  let := CompactSphereCarrier.law_probability hn
  let ν := compactBlockMeasure n k θ
  have : IsFiniteMeasure ν := inferInstanceAs
    (IsFiniteMeasure ((Measure.pi (fun _ : Fin k => CompactSphereCarrier.law n)).restrict
      {y | (fun i => (y i : Vector n)) ∈ overlapBlock 0 θ}))
  have : NeZero ν := ⟨compactBlockMeasure_nonzero hn
    (zero_overlapBlock_volume_positive hnk hk hθ)⟩
  let x : Fin k → (Fin k → CompactSphereCarrier.Carrier n) → Vector n :=
    fun i v => (v i : Vector n)
  have hx : ∀ i, Continuous (x i) := fun i => continuous_subtype_val.comp (continuous_apply i)
  have hh := expected_centralLatitude_logPartition_lower hn ν μ β hq u hu e he x hx
  have hc (J : Disorder (n + 1) μ.maxDegree) :
      (∫ v, Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (x i v)) -
          field (mixtureCoefficients μ) J (Real.sqrt q • u))) ∂ν) =
        centralLatitudePartition k μ β q θ u e J := by
    dsimp only [ν, compactBlockMeasure, x, centralLatitudePartition]
    refine replicated_compactSphere_integral hn (overlapBlock_measurable 0 θ)
      (fun y : Fin k → Vector n => Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
          field (mixtureCoefficients μ) J (Real.sqrt q • u)))) ?_
    exact (Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ =>
      ((field_contDiff _ J).continuous.comp
        ((latitudeMap_continuous u e _).comp (continuous_apply i))).sub
          continuous_const).const_mul β)).measurable
  let b := β * Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ))
  let R := physicalResidualMixture μ q hq
  have hr (J : Disorder n R.maxDegree) :
      (∫ v, Real.exp (b * ∑ i : Fin k,
        field (mixtureCoefficients R) J (x i v)) ∂ν) =
        replicatedBandPartition k R b 0 1 θ J (0 : Vector n) := by
    unfold replicatedBandPartition
    rw [LiteratureSubagBandLowerResidual.replicatedBand_zero_eq_overlapBlock]
    simp only [field_zero, sub_zero]
    dsimp only [ν, compactBlockMeasure, x]
    refine replicated_compactSphere_integral hn (overlapBlock_measurable 0 θ)
      (fun y : Fin k → Vector n => Real.exp (b * ∑ i : Fin k,
        field (mixtureCoefficients R) J (y i))) ?_
    exact (Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ =>
      (field_contDiff _ J).continuous.comp (continuous_apply i)).const_mul b)).measurable
  change (∫ J, Real.log (∫ v, Real.exp (b * ∑ i : Fin k,
    field (mixtureCoefficients R) J (x i v)) ∂ν) ∂disorderLaw n R.maxDegree) ≤ _ at hh
  simp_rw [hr, hc] at hh
  have h := div_le_div_of_nonneg_right hh
    (show 0 ≤ ((n + 1 : ℕ) : ℝ) * (k : ℝ) by positivity)
  rw [integral_div]
  convert h using 1
  unfold residualReplicatedPressure expectedReplicatedBandPressure replicatedBandPressure
  rw [integral_div]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rfl

private theorem finite_logPartition_lipschitz {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V)
    [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (GaussianSpinInterpolation.logPartition ν L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).differentiable
      (by norm_num))
  intro w
  rw [(GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
  apply (NNReal.coe_le_coe).mp
  change ‖GaussianSpinInterpolation.score ν L w‖ ≤ (K.toNNReal : ℝ)
  rw [Real.coe_toNNReal K hK]
  exact GaussianSpinInterpolation.norm_score_le ν L hL hK hb w

private theorem finite_logPartition_linear_integrable {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V)
    [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    Integrable (fun w => GaussianSpinInterpolation.logPartition ν L (T w))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  let f := GaussianSpinInterpolation.logPartition ν L
  have hf := finite_logPartition_lipschitz ν L hL hK hb
  have hbound (w : EuclideanSpace ℝ ι) :
      ‖f (T w)‖ ≤ K * ‖T‖ * ‖w‖ + ‖f 0‖ := by
    have h := hf.norm_sub_le (T w) 0
    rw [Real.coe_toNNReal K hK, sub_zero] at h
    calc
      _ ≤ ‖f (T w) - f 0‖ + ‖f 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f (T w) - f 0) (f 0)
      _ ≤ K * ‖T w‖ + ‖f 0‖ := add_le_add h le_rfl
      _ ≤ K * (‖T‖ * ‖w‖) + ‖f 0‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (T.le_opNorm w) hK) le_rfl
      _ = _ := by ring
  apply (((IsGaussian.integrable_id
    (μ := stdGaussian (EuclideanSpace ℝ ι))).norm.const_mul (K * ‖T‖)).add
      (integrable_const ‖f 0‖)).mono'
    (hf.continuous.comp T.continuous).aestronglyMeasurable
  exact .of_forall hbound


private theorem compact_replicated_log_integrable
    {V : Type*} [TopologicalSpace V] [CompactSpace V]
    [MeasurableSpace V] [BorelSpace V] {N P k : ℕ}
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (c : Degree P → ℝ) (β : ℝ) (m : Vector N)
    (z : Fin k → V → Vector N) (hz : ∀ i, Continuous (z i)) :
    Integrable (fun J : Disorder N P => Real.log (∫ v, Real.exp (β * ∑ i : Fin k,
      (field c J (z i v) - field c J m)) ∂ν)) (disorderLaw N P) := by
  let L : V → EuclideanDisorder N P →L[ℝ] ℝ := fun v =>
    β • ∑ i : Fin k, (sphereLinear c (z i v) - sphereLinear c m)
  have hs : Continuous (sphereLinear (N := N) c) :=
    (innerSL ℝ).continuous.comp (fieldFeature_continuous c)
  have hL : Continuous L := by
    exact (continuous_finsetSum _ fun i _ =>
      (hs.comp (hz i)).sub continuous_const).const_smul β
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hL.continuousOn
  have hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ max K 0 :=
    .of_forall fun v => (hK v (mem_univ v)).trans (le_max_left _ _)
  have hi := finite_logPartition_linear_integrable ν L hL.measurable
    (le_max_right _ _) hb (ContinuousLinearMap.id ℝ (EuclideanDisorder N P))
  have hic := (actual_flattened_gaussian N P).integrable_comp hi
  convert hic using 1
  funext J
  unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
  congr 1
  apply integral_congr_ae
  exact .of_forall fun v => by
    simp only [ContinuousLinearMap.id_apply, L,
      GaussianSpinInterpolation.weight, one_mul, _root_.smul_apply,
      _root_.sum_apply, _root_.sub_apply, smul_eq_mul, sphereLinear_apply,
      unpack_euclideanDisorder]

private theorem compact_restriction_nonzero {N k : ℕ} (hN : 1 ≤ N)
    {A : Set (Fin k → Vector N)} (hA : MeasurableSet A)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) A) :
    (Measure.pi (fun _ : Fin k => CompactSphereCarrier.law N)).restrict
      {y | (fun i => (y i : Vector N)) ∈ A} ≠ 0 := by
  let := CompactSphereCarrier.law_probability hN
  intro hz
  have hi := replicated_compactSphere_integral hN hA
    (fun _ : Fin k → Vector N => (1 : ℝ)) measurable_const
  rw [hz, integral_zero_measure] at hi
  have hpos : 0 < ∫ _y in A, (1 : ℝ) ∂Measure.pi (fun _ : Fin k => sphereLaw N) := by
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] using (ENNReal.toReal_pos hvol.ne' (measure_ne_top _ _))
  linarith

private theorem centralLatitude_log_integrable {n k : ℕ} (hnk : k + 1 ≤ n)
    (hk : 1 ≤ k) (μ : FiniteMixture) (β q : ℝ) {θ : ℝ} (hθ : 0 < θ)
    (u : Vector (n + 1)) (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) :
    Integrable (fun J => Real.log (centralLatitudePartition k μ β q θ u e J))
      (disorderLaw (n + 1) μ.maxDegree) := by
  have hn : 1 ≤ n := by omega
  let := CompactSphereCarrier.law_probability hn
  let ν := compactBlockMeasure n k θ
  have : IsFiniteMeasure ν := inferInstanceAs
    (IsFiniteMeasure ((Measure.pi (fun _ : Fin k => CompactSphereCarrier.law n)).restrict
      {y | (fun i => (y i : Vector n)) ∈ overlapBlock 0 θ}))
  have : NeZero ν := ⟨compactBlockMeasure_nonzero hn
    (zero_overlapBlock_volume_positive hnk hk hθ)⟩
  let z : Fin k → (Fin k → CompactSphereCarrier.Carrier n) → Vector (n + 1) :=
    fun i v => latitudeMap u e (Real.sqrt q) (v i)
  have hz : ∀ i, Continuous (z i) := fun i => (latitudeMap_continuous u e _).comp
    (continuous_subtype_val.comp (continuous_apply i))
  have hi := compact_replicated_log_integrable ν (mixtureCoefficients μ) β
    (Real.sqrt q • u) z hz
  convert hi using 1
  funext J
  congr 1
  symm
  dsimp only [ν, compactBlockMeasure, z, centralLatitudePartition]
  refine replicated_compactSphere_integral hn (overlapBlock_measurable 0 θ)
    (fun y : Fin k → Vector n => Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
        field (mixtureCoefficients μ) J (Real.sqrt q • u)))) ?_
  exact (Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ =>
    ((field_contDiff _ J).continuous.comp
      ((latitudeMap_continuous u e _).comp (continuous_apply i))).sub
        continuous_const).const_mul β)).measurable

private theorem replicatedBand_log_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ ρ m)) :
    Integrable (fun J => Real.log (replicatedBandPartition k μ β q δ ρ J m))
      (disorderLaw N μ.maxDegree) := by
  let := CompactSphereCarrier.law_probability hN
  let A := ReplicatedBand k q δ ρ m
  let ν := (Measure.pi (fun _ : Fin k => CompactSphereCarrier.law N)).restrict
    {y | (fun i => (y i : Vector N)) ∈ A}
  have : NeZero ν := ⟨compact_restriction_nonzero hN
    (replicatedBand_measurable q δ ρ m) hvol⟩
  let z : Fin k → (Fin k → CompactSphereCarrier.Carrier N) → Vector N := fun i v => v i
  have hz : ∀ i, Continuous (z i) := fun i => continuous_subtype_val.comp (continuous_apply i)
  have hi := compact_replicated_log_integrable ν (mixtureCoefficients μ) β m z hz
  convert hi using 1
  funext J
  congr 1
  symm
  dsimp only [ν, A, z, replicatedBandPartition]
  refine replicated_compactSphere_integral hN (replicatedBand_measurable q δ ρ m)
    (fun y : Fin k → Vector N => Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (y i) - field (mixtureCoefficients μ) J m))) ?_
  exact (Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ =>
    ((field_contDiff _ J).continuous.comp (continuous_apply i)).sub
      continuous_const).const_mul β)).measurable


private theorem centralLatitudePartition_pos {n k : ℕ} (hnk : k + 1 ≤ n)
    (hk : 1 ≤ k) (μ : FiniteMixture) (β q : ℝ) {θ : ℝ} (hθ : 0 < θ)
    (u : Vector (n + 1)) (e : Vector n →ₗᵢ[ℝ] Vector (n + 1))
    (J : Disorder (n + 1) μ.maxDegree) :
    0 < centralLatitudePartition k μ β q θ u e J := by
  have hn : 1 ≤ n := by omega
  have hvol := zero_overlapBlock_volume_positive hnk hk hθ
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw n)) (overlapBlock 0 θ)) := ⟨hvol.ne'⟩
  have hi : Integrable (fun x : Vector n => Real.exp (β *
      (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) x) -
        field (mixtureCoefficients μ) J (Real.sqrt q • u)))) (sphereLaw n) :=
    partition_integrand_integrable hn β
      (((field_contDiff _ J).continuous.comp (latitudeMap_continuous u e _)).sub continuous_const)
  have hp := Integrable.fintype_prod (fun _ : Fin k => hi)
  have he : (fun y : Fin k → Vector n => ∏ i : Fin k, Real.exp (β *
      (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
        field (mixtureCoefficients μ) J (Real.sqrt q • u)))) =
      fun y => Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
          field (mixtureCoefficients μ) J (Real.sqrt q • u))) := by
    ext y
    rw [Finset.mul_sum, Real.exp_sum]
  rw [he] at hp
  exact integral_exp_pos hp.restrict

private theorem latitude_window_mass_pos {n : ℕ} (hn : 2 ≤ n)
    {q η : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ)) :
    0 < (sphereLaw (n + 1)).real (overlapRegion u {r | |r - Real.sqrt q| ≤ η}) := by
  have ha : Real.sqrt q ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.sqrt_pos.mpr hq.1, (by nlinarith [Real.sq_sqrt hq.1.le, Real.sqrt_nonneg q, hq.2])⟩
  obtain ⟨C, hC, hmass⟩ := latitude_slab_mass_lower ha hη
  exact (mul_pos hC (Real.exp_pos _)).trans_le (hmass n hn u hu)

/-- Finite expected thick-latitude comparison with the actual replica
restriction and an unconditional, dimension-independent variation cost. -/
private theorem expected_replicatedBandPressure_lower_of_latitude {n k : ℕ}
    (hn : 2 ≤ n) (hnk : k + 1 ≤ n) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β : ℝ) {q δ ρ θ η : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hθ : 0 < θ)
    (hηa : η < Real.sqrt q) (hη1 : η < 1 - Real.sqrt q)
    (hηδ : η ≤ δ) (hwidth : 2 * η + θ ≤ ρ)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ)) :
    Real.log ((sphereLaw (n + 1)).real
        (overlapRegion u {r | |r - Real.sqrt q| ≤ η})) / ((n + 1 : ℕ) : ℝ) +
      residualReplicatedPressure μ β q θ hq k n -
        2 * |β| * derivativeMean (mixtureCoefficients μ) * Real.sqrt η ≤
      expectedReplicatedBandPressure k μ β q δ ρ (Real.sqrt q • u) := by
  let M := (sphereLaw (n + 1)).real (overlapRegion u {r | |r - Real.sqrt q| ≤ η})
  let D := ((n + 1 : ℕ) : ℝ) * (k : ℝ)
  let L := Real.log M / ((n + 1 : ℕ) : ℝ)
  let Z := centralLatitudePartition k μ β q θ u (latitudeFrameAt u)
  let E := fun J : Disorder (n + 1) μ.maxDegree =>
    2 * |β| * derivativeEnvelope (mixtureCoefficients μ) J * Real.sqrt η
  have hM : 0 < M := latitude_window_mass_pos hn hq hη u hu
  have hD : 0 < D := mul_pos (by positivity) (Nat.cast_pos.mpr (by omega))
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsample (J : Disorder (n + 1) μ.maxDegree) :
      L + Real.log (Z J) / D - E J ≤
        replicatedBandPressure k μ β q δ ρ J (Real.sqrt q • u) := by
    have hZ : 0 < Z J := centralLatitudePartition_pos hnk hk μ β q hθ u _ J
    have hpart := replicatedBandPartition_lower_of_latitude (k := k) hn μ β hq hηa hη1
      hηδ hwidth u hu J
    have hpos : 0 < Real.exp (-(E J) * D) * M ^ k * Z J := by positivity
    have hlog := Real.log_le_log hpos hpart
    rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero _ hM.ne')) hZ.ne',
      Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hM.ne'),
      Real.log_exp, Real.log_pow] at hlog
    change _ ≤ Real.log (replicatedBandPartition k μ β q δ ρ J (Real.sqrt q • u)) / D
    apply (le_div_iff₀ hD).mpr
    have hLD : L * D = (k : ℝ) * Real.log M := by
      dsimp only [L, D]
      field_simp
    have hZD : Real.log (Z J) / D * D = Real.log (Z J) := div_mul_cancel₀ _ hD.ne'
    dsimp only [M, Z, E, D] at hlog
    nlinarith [hLD, hZD]
  have hiZ := (centralLatitude_log_integrable hnk hk μ β q hθ u (latitudeFrameAt u)).div_const D
  have hiE := ((derivativeEnvelope_integrable (by omega : 1 ≤ n + 1)
    (mixtureCoefficients μ)).const_mul (2 * |β|)).mul_const (Real.sqrt η)
  have hδ : 0 < δ := hη.trans_le hηδ
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity : 0 < 2 * η + θ) hwidth
  have hvol := SourcePureSection9SmallClosures.replicatedBand_volume_positive
    (by omega : k + 1 ≤ n + 1) hk hq hδ hρ (Real.sqrt q • u)
    (by rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hq.1.le, hu]; ring)
  have hiB := (replicatedBand_log_integrable (by omega : 1 ≤ n + 1) μ β q δ ρ
    (Real.sqrt q • u) hvol).div_const D
  have hiLower := ((integrable_const L).add hiZ).sub hiE
  have hh := integral_mono hiLower hiB hsample
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  rw [integral_sub (f := fun J => L + Real.log (Z J) / D) (g := E)
      ((integrable_const L).add hiZ) hiE,
    integral_add (f := fun _ => L) (g := fun J => Real.log (Z J) / D)
      (integrable_const L) hiZ, integral_const, probReal_univ, one_smul] at hh
  have hE : (∫ J, E J ∂disorderLaw (n + 1) μ.maxDegree) ≤
      2 * |β| * derivativeMean (mixtureCoefficients μ) * Real.sqrt η := by
    dsimp only [E]
    rw [integral_mul_const, integral_const_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (expected_derivativeEnvelope_le (by omega : 1 ≤ n + 1) (mixtureCoefficients μ))
        (by positivity)) (Real.sqrt_nonneg _)
  have hr := residualReplicatedPressure_le_expected_centralLatitude hnk hk μ β hq hθ
    u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu)
  change L + residualReplicatedPressure μ β q θ hq k n - _ ≤ _
  change _ ≤ expectedReplicatedBandPressure k μ β q δ ρ (Real.sqrt q • u) at hh
  linarith


/-- Subag's expected thick-latitude lower comparison, with every fixed
replica count and both original band tolerances. No tail hypothesis is needed. -/
theorem expectedThickLatitudeLowerComparison (μ : FiniteMixture) (β : ℝ) :
    ExpectedThickLatitudeLowerComparison μ β := by
  intro q hq δ ρ hδ hρ k hk ε hε
  have ha : Real.sqrt q ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.sqrt_pos.mpr hq.1, (by nlinarith [Real.sq_sqrt hq.1.le, Real.sqrt_nonneg q, hq.2])⟩
  let C := 2 * |β| * (|derivativeMean (mixtureCoefficients μ)| + 1) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let t := ε / (4 * C)
  have ht : 0 < t := by dsimp only [t]; positivity
  let η := min (δ / 2) (min (ρ / 8)
    (min (Real.sqrt q / 2) (min ((1 - Real.sqrt q) / 2) (t ^ 2))))
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by linarith [ha.1]) (lt_min (by linarith [ha.2]) (sq_pos_of_pos ht))))
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηρ : η ≤ ρ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hηa : η ≤ Real.sqrt q / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη1 : η ≤ (1 - Real.sqrt q) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hηt : η ≤ t ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hsqrt : Real.sqrt η ≤ t := by
    have hs := Real.sq_sqrt hη.le
    nlinarith [Real.sqrt_nonneg η, ht]
  have hcoef : 2 * |β| * derivativeMean (mixtureCoefficients μ) ≤ C := by
    dsimp only [C]
    have h := mul_le_mul_of_nonneg_left
      (le_abs_self (derivativeMean (mixtureCoefficients μ))) (by positivity : 0 ≤ 2 * |β|)
    nlinarith [abs_nonneg β]
  have hcost : 2 * |β| * derivativeMean (mixtureCoefficients μ) * Real.sqrt η ≤ ε / 2 := by
    calc
      _ ≤ C * Real.sqrt η := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg η)
      _ ≤ C * t := mul_le_mul_of_nonneg_left hsqrt hC.le
      _ = ε / 4 := by dsimp only [t]; field_simp
      _ ≤ ε / 2 := by linarith
  refine ⟨ρ / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (k + 1), eventually_ge_atTop (2 : ℕ),
    latitude_slab_entropy_eventually_lower ha hη (show 0 < ε / 2 by positivity)]
    with n hnk hn hent
  have hu := latitudeChartPole_norm_sq n
  have he := hent (latitudeChartPole n) hu
  rw [Real.sq_sqrt hq.1.le] at he
  have hf := expected_replicatedBandPressure_lower_of_latitude hn hnk hk μ β hq
    hη (show 0 < ρ / 2 by positivity) (by linarith [ha.1]) (by linarith [ha.2])
    (show η ≤ δ by linarith) (show 2 * η + ρ / 2 ≤ ρ by linarith)
    (latitudeChartPole n) hu
  change Real.log (1 - q) / 2 + residualReplicatedPressure μ β q (ρ / 2) hq k n - ε ≤
    expectedReplicatedBandPressure k μ β q δ ρ (Real.sqrt q • latitudeChartPole n)
  linarith

/-- The lower approximation now has only the separate residual replicated
limit as its analytic dependency. -/
theorem expectedBandLowerApproximation_of_residualLimit
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hresidual : ResidualReplicatedLimit D) : ExpectedBandLowerApproximation D :=
  expectedBandLowerApproximation_of_residual_and_thickLatitude D hresidual
    (expectedThickLatitudeLowerComparison μ β)

end SlowEquilibration.LiteratureSubagThickLatitudeLower
