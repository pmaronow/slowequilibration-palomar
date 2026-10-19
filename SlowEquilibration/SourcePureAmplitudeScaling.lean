-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferFiniteMixtureLiterature

/-! Exact amplitude scaling discharges the pure branch of source
`thm:pc-capture` and hence the finite-mixture main theorem. Identifying the
maximal degrees keeps the same Gaussian tensors; the certificate, marks,
logarithmic center and critical-center bands then scale exactly.

The directing-norm theorem is applied at the original amplitude before its
conclusion is transported through the full replica laws. Only Proposition 24
is transported as a literature hypothesis, so no comparison of chosen
thermodynamic-data structures is needed. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureAmplitudeScaling

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalMarkedWindows TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SourceConditionedCPTransferInitialAdapter
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SphericalGaussianJet SphericalForm SourceReductionClosedBandGraph
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pure_minDegree (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) :
    (FiniteMixture.pure p hp c hc).minDegree = p := by
  simp [FiniteMixture.minDegree, FiniteMixture.pure,
    Finsupp.support_single p hc.ne']

private theorem pure_maxDegree (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) :
    (FiniteMixture.pure p hp c hc).maxDegree = p := by
  simp [FiniteMixture.maxDegree, FiniteMixture.pure,
    Finsupp.support_single p hc.ne']

/-- The CS contact potential depends only on the temperature-weighted covariance. -/
private theorem potential_eq_of_weighted_xi_eq (μ ν : FiniteMixture) (β β' : ℝ)
    (hxi : ∀ r : ℝ, β ^ 2 * μ.xi r = β' ^ 2 * ν.xi r)
    (ζ : Measure ℝ) :
    CSStructure.potential μ β ζ = CSStructure.potential ν β' ζ := by
  funext r
  unfold CSStructure.potential CrisantiSommers.firstVariation
  rw [hxi r]

/-- Changing a pure covariance amplitude is exactly a change of temperature. -/
private theorem pure_weighted_xi (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (β r : ℝ) :
    β ^ 2 * (FiniteMixture.pure p hp c hc).xi r =
      (β * Real.sqrt c) ^ 2 *
        (FiniteMixture.pure p hp 1 zero_lt_one).xi r := by
  rw [FiniteMixture.pure_xi, FiniteMixture.pure_xi, mul_pow,
    Real.sq_sqrt hc.le]
  ring

/-- The strict source certificate has the same contact and curvature after scaling. -/
private theorem pure_certificate (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp c hc) β x Q) :
    Certificate (FiniteMixture.pure p hp 1 zero_lt_one)
      (β * Real.sqrt c) x Q := by
  have hpot := potential_eq_of_weighted_xi_eq _ _ β (β * Real.sqrt c)
    (pure_weighted_xi p hp c hc β) (twoAtom x Q)
  refine ⟨?_, mul_pos h.beta_pos (Real.sqrt_pos.2 hc), h.weight_range,
    h.overlap_range, ?_, ?_, ?_, ?_⟩
  · simpa only [pure_minDegree] using h.min_degree
  · rw [← hpot]; exact h.contact_value
  · rw [← hpot]; exact h.contact_derivative
  · rw [← hpot]; exact h.positive_off_contact
  · rw [← hpot]; exact h.contact_curvature

/-- Reindexing the maximal degree identifies the same independent Gaussian tensors. -/
private def disorderEquiv {N P R : ℕ} (hPR : P = R) :
    Disorder N P ≃ᵐ Disorder N R := by
  subst R
  exact MeasurableEquiv.refl _

private theorem disorderEquiv_measurePreserving {N P R : ℕ} (hPR : P = R) :
    MeasurePreserving (disorderEquiv (N := N) hPR)
      (disorderLaw N P) (disorderLaw N R) := by
  subst R
  exact MeasurePreserving.id _

private theorem field_scale {N P : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (c : Degree P → ℝ) (J : Disorder N P) (u : Vector N) :
    field (fun d => a * c d) J u = Real.sqrt a * field c J u := by
  unfold field
  simp_rw [Real.sqrt_mul ha]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Pure amplitudes use precisely the same disorder after identifying their degrees. -/
private def pureDisorderEquiv (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) :
    Disorder N (FiniteMixture.pure p hp c hc).maxDegree ≃ᵐ
      Disorder N (FiniteMixture.pure p hp 1 zero_lt_one).maxDegree :=
  disorderEquiv ((pure_maxDegree p hp c hc).trans
    (pure_maxDegree p hp 1 zero_lt_one).symm)

private theorem field_scale_reindex {N P R : ℕ} (hPR : P = R)
    (a : ℝ) (ha : 0 ≤ a) (c : Degree P → ℝ) (d : Degree R → ℝ)
    (hcd : ∀ k : ℕ, ∀ (hkP : k < P + 1) (hkR : k < R + 1) (hk : 2 ≤ k),
      c ⟨⟨k, hkP⟩, hk⟩ = a * d ⟨⟨k, hkR⟩, hk⟩)
    (J : Disorder N P) (u : Vector N) :
    field c J u = Real.sqrt a * field d (disorderEquiv hPR J) u := by
  subst R
  have heq : c = fun k => a * d k := by
    funext k
    exact hcd k.val.val k.val.isLt k.val.isLt k.property
  rw [heq]
  exact field_scale a ha d J u

/-- Pathwise amplitude scaling of the literal original Hamiltonian. -/
private theorem pure_field (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) :
    field (mixtureCoefficients (FiniteMixture.pure p hp c hc)) J u =
      Real.sqrt c *
        field (mixtureCoefficients (FiniteMixture.pure p hp 1 zero_lt_one))
          (pureDisorderEquiv N p hp c hc J) u := by
  apply field_scale_reindex _ c hc.le
  intro k _ _ _
  by_cases hk : k = p <;>
    simp [mixtureCoefficients, FiniteMixture.pure, hk]

/-- The ordinary CS functional is unchanged by weighted covariance equality. -/
private theorem functional_eq_of_weighted_xi_eq (μ ν : FiniteMixture) (β β' : ℝ)
    (hxi : ∀ r : ℝ, β ^ 2 * μ.xi r = β' ^ 2 * ν.xi r)
    (ζ : Measure ℝ) (q : ℝ) :
    functional β μ.xi ζ q = functional β' ν.xi ζ q := by
  have hi : β ^ 2 * (∫ s, μ.xi s ∂ζ) = β' ^ 2 * (∫ s, ν.xi s ∂ζ) := by
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (.of_forall hxi)
  unfold functional
  rw [mul_sub, mul_sub, hxi 1, hi]

/-- The variational pressure is unchanged by exact covariance-temperature scaling. -/
private theorem variationalValue_eq_of_weighted_xi_eq (μ ν : FiniteMixture) (β β' : ℝ)
    (hxi : ∀ r : ℝ, β ^ 2 * μ.xi r = β' ^ 2 * ν.xi r) :
    CSParisiMeasure.variationalValue μ β = CSParisiMeasure.variationalValue ν β' := by
  have hv (ζ : Admissible) : ζ.value β μ.xi = ζ.value β' ν.xi :=
    functional_eq_of_weighted_xi_eq μ ν β β' hxi ζ.law ζ.cutoff
  apply le_antisymm
  · exact (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β _).trans_eq
      (hv (CSParisiMeasure.canonicalMinimizer ν β'))
  · exact (CSParisiMeasure.canonicalMinimizer_isMinimizer ν β' _).trans_eq
      (hv (CSParisiMeasure.canonicalMinimizer μ β)).symm

private theorem pure_xi1_scale (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (r : ℝ) :
    (FiniteMixture.pure p hp c hc).xi1 r =
      c * (FiniteMixture.pure p hp 1 zero_lt_one).xi1 r := by
  simp [FiniteMixture.xi1, FiniteMixture.pure, Finsupp.support_single p hc.ne',
    mul_assoc]

private theorem pure_xi2_scale (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (r : ℝ) :
    (FiniteMixture.pure p hp c hc).xi2 r =
      c * (FiniteMixture.pure p hp 1 zero_lt_one).xi2 r := by
  simp [FiniteMixture.xi2, FiniteMixture.curvatureCoeff, FiniteMixture.pure,
    Finsupp.support_single p hc.ne', mul_assoc]

/-- The energy mark scales by the positive field amplitude. -/
private theorem pure_markE (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (β x Q : ℝ) :
    markE (FiniteMixture.pure p hp c hc) β x Q =
      Real.sqrt c * markE (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) x Q := by
  unfold markE markA markY
  rw [pure_xi1_scale, FiniteMixture.pure_xi, FiniteMixture.pure_xi]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring_nf
  rw [Real.sq_sqrt hc.le]
  ring

/-- The radial mark scales by the same positive field amplitude. -/
private theorem pure_markK (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (β Q : ℝ) :
    markK (FiniteMixture.pure p hp c hc) β Q =
      Real.sqrt c * markK (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) Q := by
  unfold markK markB markY
  rw [pure_xi2_scale]
  field_simp
  rw [Real.sq_sqrt hc.le]
  ring

/-- The printed logarithmic center scales exactly, including its logarithmic term. -/
private theorem sourcePureAnalyticCenter_scale (N : ℕ) (E t s : ℝ) (hs : s ≠ 0) :
    sourcePureAnalyticCenter N (s * E) t =
      s * sourcePureAnalyticCenter N E (t * s) := by
  unfold sourcePureAnalyticCenter
  field_simp

private theorem gibbsLaw_eq_of_weighted_field_eq {N : ℕ}
    (β β' : ℝ) (H H' : Vector N → ℝ)
    (hH : ∀ u, β * H u = β' * H' u) :
    gibbsLaw N β H = gibbsLaw N β' H' := by
  have hp : partition N β H = partition N β' H' := by
    unfold partition
    simp_rw [hH]
  simp only [gibbsLaw, gibbsDensity, hp, hH]

/-- The Gibbs measures agree on each common realization of the Gaussian tensors. -/
private theorem pure_gibbsLaw (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (β : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) :
    mixtureGibbsLaw (FiniteMixture.pure p hp c hc) β J =
      mixtureGibbsLaw (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) (pureDisorderEquiv N p hp c hc J) := by
  apply gibbsLaw_eq_of_weighted_field_eq
  intro u
  unfold fieldOfMixture
  rw [pure_field]
  ring

private theorem replica_law_transport
    {Ω Ω' V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace V]
    (d : Measure Ω) (d' : Measure Ω')
    (G : Kernel Ω V) (G' : Kernel Ω' V)
    [IsMarkovKernel G] [IsMarkovKernel G']
    (f : Ω → Ω') (hf : MeasurePreserving f d d')
    (hG : ∀ ω, G ω = G' (f ω)) (m : ℕ) :
    GaussianReplicaKernel.law d G m = GaussianReplicaKernel.law d' G' m := by
  apply Measure.ext
  intro s hs
  change (Measure.bind d (GaussianReplicaKernel.iid G m)) s =
    (Measure.bind d' (GaussianReplicaKernel.iid G' m)) s
  rw [Measure.bind_apply hs (GaussianReplicaKernel.iid G m).aemeasurable,
    Measure.bind_apply hs (GaussianReplicaKernel.iid G' m).aemeasurable]
  calc
    _ = ∫⁻ ω, GaussianReplicaKernel.iid G' m (f ω) s ∂d := by
      apply lintegral_congr
      intro ω
      rw [GaussianReplicaKernel.iid_apply, GaussianReplicaKernel.iid_apply, hG ω]
    _ = _ := hf.lintegral_comp ((GaussianReplicaKernel.iid G' m).measurable_coe hs)

private theorem pure_replica_law (N k p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (β : ℝ) :
    GaussianReplicaKernel.law (disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree)
      (allDimensionGibbsKernel (mixtureCoefficients (FiniteMixture.pure p hp c hc)) β) k =
    GaussianReplicaKernel.law
      (disorderLaw N (FiniteMixture.pure p hp 1 zero_lt_one).maxDegree)
      (allDimensionGibbsKernel
        (mixtureCoefficients (FiniteMixture.pure p hp 1 zero_lt_one))
        (β * Real.sqrt c)) k := by
  apply replica_law_transport _ _ _ _ (pureDisorderEquiv N p hp c hc)
    (disorderEquiv_measurePreserving _)
  intro J
  rw [allDimensionGibbsKernel_apply, allDimensionGibbsKernel_apply]
  apply gibbsLaw_eq_of_weighted_field_eq
  intro u
  rw [pure_field]
  ring

private theorem pure_physicalFullOverlapLaw (n m p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (β : ℝ) :
    physicalFullOverlapLaw (n := n) (m := m) (FiniteMixture.pure p hp c hc) β =
      physicalFullOverlapLaw (n := n) (m := m) (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) := by
  have hlaw : physicalReplicaLaw (n := n) (m := m) (FiniteMixture.pure p hp c hc) β =
      physicalReplicaLaw (n := n) (m := m) (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) := pure_replica_law (n+2) m p hp c hc β
  unfold physicalFullOverlapLaw
  exact congrArg
    (fun v : ProbabilityMeasure (Fin m → Vector (n+2)) =>
      v.map physicalFullOverlapCoordinates)
    ((Measure.toProbabilityMeasure_inj _ _).2 hlaw)

private theorem pure_directingNorm (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (β Q : ℝ)
    (hnorm : PhysicalDirectingNormQ (FiniteMixture.pure p hp c hc) β Q) :
    PhysicalDirectingNormQ (FiniteMixture.pure p hp 1 zero_lt_one)
      (β * Real.sqrt c) Q := by
  have harray : physicalFullOverlapLawArray (FiniteMixture.pure p hp c hc) β =
      physicalFullOverlapLawArray (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) := by
    funext n m
    exact pure_physicalFullOverlapLaw n m p hp c hc β
  have hset : physicalFullAsymptoticLimitSet (FiniteMixture.pure p hp c hc) β =
      physicalFullAsymptoticLimitSet (FiniteMixture.pure p hp 1 zero_lt_one)
        (β * Real.sqrt c) := by
    unfold physicalFullAsymptoticLimitSet
    rw [harray]
  unfold PhysicalDirectingNormQ at *
  rwa [hset] at hnorm

private theorem replicatedBandPressure_eq_of_field_identification
    (μ ν : FiniteMixture) (β β' : ℝ) {N : ℕ}
    (e : Disorder N μ.maxDegree ≃ᵐ Disorder N ν.maxDegree)
    (hH : ∀ J u, β * field (mixtureCoefficients μ) J u =
      β' * field (mixtureCoefficients ν) (e J) u)
    (k : ℕ) (q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    replicatedBandPressure k μ β q δ ρ J m =
      replicatedBandPressure k ν β' q δ ρ (e J) m := by
  have hp : replicatedBandPartition k μ β q δ ρ J m =
      replicatedBandPartition k ν β' q δ ρ (e J) m := by
    unfold replicatedBandPartition
    apply integral_congr_ae
    filter_upwards [] with σ
    congr 1
    simp only [Finset.mul_sum, mul_sub]
    apply Finset.sum_congr rfl
    intro i _
    rw [hH J (σ i), hH J m]
  unfold replicatedBandPressure
  rw [hp]

private theorem expectedReplicatedBandPressure_eq_of_field_identification
    (μ ν : FiniteMixture) (β β' : ℝ) {N : ℕ}
    (e : Disorder N μ.maxDegree ≃ᵐ Disorder N ν.maxDegree)
    (hE : MeasurePreserving e (disorderLaw N μ.maxDegree) (disorderLaw N ν.maxDegree))
    (hH : ∀ J u, β * field (mixtureCoefficients μ) J u =
      β' * field (mixtureCoefficients ν) (e J) u)
    (k : ℕ) (q δ ρ : ℝ) (m : Vector N) :
    expectedReplicatedBandPressure k μ β q δ ρ m =
      expectedReplicatedBandPressure k ν β' q δ ρ m := by
  unfold expectedReplicatedBandPressure
  calc
    _ = ∫ J, replicatedBandPressure k ν β' q δ ρ (e J) m
        ∂disorderLaw N μ.maxDegree :=
      integral_congr_ae (.of_forall fun J =>
        replicatedBandPressure_eq_of_field_identification μ ν β β' e hH k q δ ρ J m)
    _ = _ := hE.integral_comp' (fun J => replicatedBandPressure k ν β' q δ ρ J m)

private theorem uniformDeviationEvent_eq_preimage_of_field_identification
    (μ ν : FiniteMixture) (β β' : ℝ) {N : ℕ}
    (e : Disorder N μ.maxDegree ≃ᵐ Disorder N ν.maxDegree)
    (hE : MeasurePreserving e (disorderLaw N μ.maxDegree) (disorderLaw N ν.maxDegree))
    (hH : ∀ J u, β * field (mixtureCoefficients μ) J u =
      β' * field (mixtureCoefficients ν) (e J) u)
    (k : ℕ) (q δ ρ t : ℝ) :
    uniformDeviationEvent k μ β q δ ρ t =
      e ⁻¹' uniformDeviationEvent k ν β' q δ ρ t := by
  ext J
  simp only [uniformDeviationEvent, Set.mem_ofPred_eq, Set.mem_preimage]
  simp_rw [replicatedBandPressure_eq_of_field_identification μ ν β β' e hH,
    expectedReplicatedBandPressure_eq_of_field_identification μ ν β β' e hE hH]

private theorem proposition24_of_field_identification
    (μ ν : FiniteMixture) (β β' q : ℝ) (hβ' : 0 < β')
    (e : ∀ N, Disorder N μ.maxDegree ≃ᵐ Disorder N ν.maxDegree)
    (hE : ∀ N, MeasurePreserving (e N) (disorderLaw N μ.maxDegree)
      (disorderLaw N ν.maxDegree))
    (hH : ∀ N J u, β * field (mixtureCoefficients μ) J u =
      β' * field (mixtureCoefficients ν) (e N J) u)
    (h24 : Proposition24 μ β q) : Proposition24 ν β' q := by
  refine ⟨hβ', h24.2.1, ?_⟩
  intro t c ht hc
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, k₀, h24⟩ := h24.2.2 t c ht hc
  refine ⟨δ₀, hδ₀, ρ₀, hρ₀, k₀, ?_⟩
  intro δ hδ hδ₀' ρ hρ hρ₀' k hk N hN
  obtain ⟨hm, hp⟩ := h24 δ hδ hδ₀' ρ hρ hρ₀' k hk N hN
  have hev := uniformDeviationEvent_eq_preimage_of_field_identification
    μ ν β β' (e N) (hE N) (hH N) k q δ ρ t
  rw [hev] at hm hp
  refine ⟨(e N).measurableSet_preimage.mp hm, ?_⟩
  have hreal : (disorderLaw N μ.maxDegree).real
      ((e N) ⁻¹' uniformDeviationEvent k ν β' q δ ρ t) =
      (disorderLaw N ν.maxDegree).real (uniformDeviationEvent k ν β' q δ ρ t) :=
    congrArg ENNReal.toReal ((hE N).measure_preimage_equiv _)
  rwa [hreal] at hp

private theorem pure_proposition24 (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {β Q : ℝ} (h24 : Proposition24 (FiniteMixture.pure p hp c hc) β Q) :
    Proposition24 (FiniteMixture.pure p hp 1 zero_lt_one) (β * Real.sqrt c) Q := by
  apply proposition24_of_field_identification _ _ β (β * Real.sqrt c) Q
    (mul_pos h24.1 (Real.sqrt_pos.2 hc)) (fun N => pureDisorderEquiv N p hp c hc)
    (fun _ => disorderEquiv_measurePreserving _) _ h24
  intro N J u
  rw [pure_field]
  ring

private theorem pure_center_field (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) :
    field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) J u =
      Real.sqrt c * field (centerCoefficients
        (mixtureCoefficients (FiniteMixture.pure p hp 1 zero_lt_one)) Q)
        (pureDisorderEquiv N p hp c hc J) u := by
  rw [field_center_scale _ (mixtureCoefficients_nonnegative _) hQ,
    field_center_scale _ (mixtureCoefficients_nonnegative _) hQ]
  exact pure_field N p hp c hc J _

private theorem pure_center_gradient (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) :
    surfaceGradient
      (field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) J) u =
      Real.sqrt c • surfaceGradient
        (field (centerCoefficients
          (mixtureCoefficients (FiniteMixture.pure p hp 1 zero_lt_one)) Q)
          (pureDisorderEquiv N p hp c hc J)) u := by
  rw [funext (pure_center_field N p hp c hc hQ J)]
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient, real_inner_smul_left, inner_surfaceGradient,
    fderiv_const_mul ((field_contDiff _ _).differentiable (by simp) u)]
  rfl

private theorem pure_center_radial (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) :
    actualScore (centerCoefficients
      (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) J u 1 =
      Real.sqrt c * actualScore (centerCoefficients
        (mixtureCoefficients (FiniteMixture.pure p hp 1 zero_lt_one)) Q)
        (pureDisorderEquiv N p hp c hc J) u 1 := by
  rw [pure_actualScore_radial_eq_value, pure_actualScore_radial_eq_value]
  unfold actualValue
  rw [pure_center_field N p hp c hc hQ]
  ring

private theorem scaled_mem_image {s v : ℝ} (hs : s ≠ 0) (U : Set ℝ) :
    s * v ∈ (fun k => s * k) '' U ↔ v ∈ U := by
  constructor
  · rintro ⟨k, hk, he⟩
    rwa [(mul_left_cancel₀ hs he : k = v)] at hk
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem pure_windowCenter (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 ≤ Q) (m M : ℝ) (U : Set ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) :
    (J, u) ∈ windowCenterGraph (FiniteMixture.pure p hp c hc) Q
      (Real.sqrt c * m) (Real.sqrt c * M) ((fun k => Real.sqrt c * k) '' U) ↔
    (pureDisorderEquiv N p hp c hc J, u) ∈
      windowCenterGraph (FiniteMixture.pure p hp 1 zero_lt_one) Q m M U := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  unfold windowCenterGraph
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [pure_center_gradient N p hp c hc hQ, pure_center_field N p hp c hc hQ,
    pure_center_radial N p hp c hc hQ]
  simp only [smul_eq_zero, hs.ne', false_or, scaled_mem_image hs.ne']
  rw [← mul_sub, ← mul_add]
  simp only [Set.mem_Icc, mul_le_mul_iff_right₀ hs]

private theorem pure_bandUnion (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 ≤ Q) (m M b : ℝ) (U : Set ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) :
    ambientWindowBandUnion (FiniteMixture.pure p hp c hc) Q
      (Real.sqrt c * m) (Real.sqrt c * M) b ((fun k => Real.sqrt c * k) '' U) J =
    ambientWindowBandUnion (FiniteMixture.pure p hp 1 zero_lt_one) Q m M b U
      (pureDisorderEquiv N p hp c hc J) := by
  ext u
  unfold ambientWindowBandUnion physicalSphereBandUnionGraph bandUnionGraph
    SourceReductionCompactBandProjection.bandUnionGraph
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  simp_rw [pure_windowCenter N p hp c hc hQ]

private theorem pure_complementMass (N p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 ≤ Q) (m M b β : ℝ) (U : Set ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) :
    originalBandComplementMass (FiniteMixture.pure p hp c hc) Q
      (Real.sqrt c * m) (Real.sqrt c * M) b β ((fun k => Real.sqrt c * k) '' U) J =
    originalBandComplementMass (FiniteMixture.pure p hp 1 zero_lt_one) Q
      m M b (β * Real.sqrt c) U (pureDisorderEquiv N p hp c hc J) := by
  unfold originalBandComplementMass
  rw [pure_gibbsLaw, pure_bandUnion N p hp c hc hQ]

private theorem pure_expected_complementMass (N p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) {Q : ℝ} (hQ : 0 ≤ Q) (m M b β : ℝ) (U : Set ℝ) :
    (∫ J, originalBandComplementMass (FiniteMixture.pure p hp c hc) Q
      (Real.sqrt c * m) (Real.sqrt c * M) b β ((fun k => Real.sqrt c * k) '' U) J
      ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree) =
    ∫ J, originalBandComplementMass (FiniteMixture.pure p hp 1 zero_lt_one) Q
      m M b (β * Real.sqrt c) U J
      ∂disorderLaw N (FiniteMixture.pure p hp 1 zero_lt_one).maxDegree := by
  simp_rw [pure_complementMass N p hp c hc hQ]
  have hE : MeasurePreserving (pureDisorderEquiv N p hp c hc)
      (disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree)
      (disorderLaw N (FiniteMixture.pure p hp 1 zero_lt_one).maxDegree) :=
    disorderEquiv_measurePreserving _
  exact hE.integral_comp'
    (fun J => originalBandComplementMass (FiniteMixture.pure p hp 1 zero_lt_one) Q
      m M b (β * Real.sqrt c) U J)

private theorem amplitude_one_capture_of_norm_and_proposition24
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 zero_lt_one) β x Q)
    (hChen : Chen2013FiniteParisi)
    (hnorm : PhysicalDirectingNormQ (FiniteMixture.pure p (by omega) 1 zero_lt_one) β Q)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 zero_lt_one) β Q) :
    PureBranchFixedWindowCapture (FiniteMixture.pure p (by omega) 1 zero_lt_one) β x Q := by
  intro _
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 zero_lt_one
  let K := markK μ β Q
  let edge := 2 * Real.sqrt (Q ^ 2 * μ.xi2 Q)
  let δ := (K - edge) / 2
  have hδ : 0 < δ := by
    have hh := h.edge_margin.2.2
    change 0 < K - edge at hh
    exact half_pos hh
  let U := Icc (K - δ) (K + δ)
  have hcontact : markK μ β Q ∈ interior U := by
    rw [show U = Icc (K - δ) (K + δ) from rfl, interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hgap : ∀ k ∈ U, 2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) < k := by
    intro k hk
    have hh := hk.1
    change K - δ ≤ k at hh
    change edge < k
    dsimp only [δ] at hδ hh
    linarith
  obtain ⟨⟨b, hb, hcapture⟩, _⟩ :=
    SourcePureCaptureLiteralConsumer.pure_consumer_capture_of_three_physical_inputs
      p hp h U hcontact hnorm
      (PureReplicaMeanEnergyAssembly.pure_physicalReplicaMeanEnergy_of_literature p hp h hChen h24)
      (PurePhysicalHighEnergyRelocation.pure_physicalHighEnergyRelocation p hp)
  refine ⟨U, b, isCompact_Icc, hcontact, hgap, hb.1, hb.2, ?_⟩
  have hh := hcapture b ⟨hb.1, le_rfl⟩
  change Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
    ∫ J, originalBandComplementMass μ Q
      ((Real.sqrt Q) ^ p * SourcePureCaptureFixedCapEstimates.pureSourceCenter p hp n)
      M b β U J ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) at hh
  simp_rw [SourcePureCaptureLiteralConsumer.pure_source_consumer_center_eq p hp h] at hh
  exact hh

/-- Exact positive-amplitude scaling discharges the pure branch of source
`thm:pc-capture` using only the certificate and the stated cited theorems. -/
theorem pureBranchFixedWindowCapture_of_cited_theorems
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    PureBranchFixedWindowCapture μ β x Q := by
  intro hnp
  obtain ⟨p, hp, c, hc, hμ⟩ :=
    SourceConditionedCPTransfer.pure_representation_of_not_nonpure μ hnp
  subst μ
  have hp4 : 4 ≤ p := by simpa only [pure_minDegree] using h.min_degree
  have h1 := pure_certificate p hp c hc h
  have hnorm := pure_directingNorm p hp c hc β Q
    (SourceLiteraturePhysicalNormQ.physicalDirectingNormQ_of_cited_theorems
      hChen hChenSen h h5 h25)
  have hcap := amplitude_one_capture_of_norm_and_proposition24 p hp4 h1 hChen hnorm
    (pure_proposition24 p hp c hc h24)
  obtain ⟨U, b, hU, hcontact, hgap, hb, hbQ, hcapture⟩ :=
    hcap (by simp only [pure_minDegree, pure_maxDegree, lt_self_iff_false, not_false_eq_true])
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨(fun k => Real.sqrt c * k) '' U, b,
    hU.image (continuous_const.mul continuous_id), ?_, ?_, hb, hbQ, ?_⟩
  · rw [pure_markK]
    have hi := (Homeomorph.mulLeft₀ (Real.sqrt c) hs.ne').image_interior U
    simp only [Homeomorph.coe_mulLeft₀] at hi
    rw [← hi]
    exact ⟨_, hcontact, rfl⟩
  · rintro k ⟨k, hk, rfl⟩
    have he : Real.sqrt (Q ^ 2 * (FiniteMixture.pure p hp c hc).xi2 Q) =
        Real.sqrt c * Real.sqrt (Q ^ 2 * (FiniteMixture.pure p hp 1 zero_lt_one).xi2 Q) := by
      rw [pure_xi2_scale, show Q ^ 2 * (c * (FiniteMixture.pure p hp 1 zero_lt_one).xi2 Q) =
        c * (Q ^ 2 * (FiniteMixture.pure p hp 1 zero_lt_one).xi2 Q) by ring,
        Real.sqrt_mul hc.le]
    rw [he]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left (hgap k hk) hs
  · have hcenter (N : ℕ) :
        sourcePureAnalyticCenter N (markE (FiniteMixture.pure p hp c hc) β x Q) (β*x) =
          Real.sqrt c * sourcePureAnalyticCenter N
            (markE (FiniteMixture.pure p hp 1 zero_lt_one) (β * Real.sqrt c) x Q)
            ((β * Real.sqrt c) * x) := by
      rw [pure_markE, sourcePureAnalyticCenter_scale N _ _ _ hs.ne']
      congr 2
      ring
    apply (hcapture.comp (tendsto_id.atTop_div_const hs)).congr'
    filter_upwards [] with M
    apply Filter.limsup_congr
    filter_upwards [] with n
    rw [hcenter]
    have heq := pure_expected_complementMass (n+2) p hp c hc h.overlap_range.1.le
      (sourcePureAnalyticCenter (n+2)
        (markE (FiniteMixture.pure p hp 1 zero_lt_one) (β * Real.sqrt c) x Q)
        ((β * Real.sqrt c) * x)) (M / Real.sqrt c) b β U
    rw [show Real.sqrt c * (M / Real.sqrt c) = M by field_simp] at heq
    exact heq.symm

/-- Source `thm:main-condensed` and the field-independent initial-law clauses
for every certified finite mixture, with no remaining pure-branch premise. -/
theorem finiteMixture_main_condensed_and_initial_of_literature
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun (J N) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact finiteMixture_main_condensed_and_initial_of_cited_theorems
    μ h hChen hChenSen h5 h25 h24
    (pureBranchFixedWindowCapture_of_cited_theorems μ h hChen hChenSen h5 h25 h24)

end SlowEquilibration.SourcePureAmplitudeScaling
