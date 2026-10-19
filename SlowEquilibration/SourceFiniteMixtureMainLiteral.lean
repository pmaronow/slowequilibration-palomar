-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureAmplitudeScaling
public import SlowEquilibration.SphericalEffectiveField
public import SlowEquilibration.SphericalFieldKernelCongruence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Source `thm:main-condensed` and `thm:main-initial`(i) for certified finite
mixtures, with independence from the literal Hamiltonian on the sphere.
The spherical restriction carries the evaluation sigma-algebra; its actual
finite-dimensional continuous-field image has the same sigma-algebra.
The constructed coefficient lift and spherical kernel congruence transport
the Haar bound without requiring independence from ambient radial terms or
redundant Gaussian tensors. One exponent serves every asymptotic clause.
The finite-dimensional expected-deficit inequality `(eq:intro-haar)` is
also restated for the original Gaussian model. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceFiniteMixtureMainLiteral

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalEffectiveField SphericalRotationCovariance SphericalReversibility SphericalDynamics
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance literalSphere_compactSpace (N : ℕ) :
    CompactSpace ({x : Vector N | OnSphere x} : Set (Vector N)) :=
  isCompact_iff_compactSpace.mp (physicalSphere_compact N)

private abbrev LiteralField (μ : FiniteMixture) (N : ℕ) :=
  Space (mixtureCoefficients μ) {x : Vector N | OnSphere x}

private def literalFieldMap (μ : FiniteMixture) (N : ℕ) :
    Disorder N μ.maxDegree →L[ℝ] LiteralField μ N :=
  project (mixtureCoefficients μ) {x : Vector N | OnSphere x}

private def literalFieldLift (μ : FiniteMixture) (N : ℕ) :
    LiteralField μ N →L[ℝ] Disorder N μ.maxDegree :=
  lift (mixtureCoefficients μ) {x : Vector N | OnSphere x}

/-- Evaluation measurability of the literal spherical function retains
exactly the Borel information in its continuous finite-dimensional image. -/
private theorem literalFieldMap_indep {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : FiniteMixture) (J : Ω → Disorder N μ.maxDegree)
    (ν : Ω → ProbabilityMeasure (Vector N))
    (hind : IndepFun
      (fun ω => fun x : {x : Vector N // OnSphere x} =>
        field (mixtureCoefficients μ) (J ω) x) ν P) :
    IndepFun (fun ω => literalFieldMap μ N (J ω)) ν P := by
  have hspace : (Subtype.instMeasurableSpace : MeasurableSpace (LiteralField μ N)) =
      MeasurableSpace.comap
        (fun H : LiteralField μ N => fun x : {x : Vector N // OnSphere x} => H.val x)
        (MeasurableSpace.pi : MeasurableSpace ({x : Vector N // OnSphere x} → ℝ)) := by
    let : CompactSpace {x : Vector N // OnSphere x} :=
      isCompact_iff_compactSpace.mp (physicalSphere_compact N)
    change MeasurableSpace.comap Subtype.val
      (inferInstance : MeasurableSpace C({x : Vector N // OnSphere x}, ℝ)) = _
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    rfl
  rw [IndepFun_iff_Indep] at hind ⊢
  rw [hspace, MeasurableSpace.comap_comp]
  exact hind

private def literalFieldDistance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (H : LiteralField μ N) (ν : ProbabilityMeasure (Vector N)) : ℝ :=
  distance μ β T (literalFieldLift μ N H) ν

private theorem literalFieldDistance_measurable {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Measurable (fun p : LiteralField μ N × ProbabilityMeasure (Vector N) =>
      literalFieldDistance μ β T p.1 p.2) := by
  exact (distance_joint_measurable hN μ β T).comp
    (((literalFieldLift μ N).measurable.comp measurable_fst).prodMk measurable_snd)

private theorem literalFieldDistance_factorization {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (ν : ProbabilityMeasure (Vector N)) (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x) :
    distance μ β T J ν =
      literalFieldDistance μ β T (literalFieldMap μ N J) ν := by
  have hf : ∀ x : Vector N, OnSphere x →
      fieldOfMixture μ J x =
        fieldOfMixture μ (literalFieldLift μ N (literalFieldMap μ N J)) x := by
    intro x hx
    exact (field_lift (mixtureCoefficients μ) {y : Vector N | OnSphere y}
      (literalFieldMap μ N J) ⟨x, hx⟩).symm
  have hκ : mixedTransitionKernel μ J β T ∘ₘ ν.toMeasure =
      mixedTransitionKernel μ (literalFieldLift μ N (literalFieldMap μ N J)) β T
        ∘ₘ ν.toMeasure := by
    apply Measure.comp_congr
    filter_upwards [hν] with x hx
    exact mixedTransitionKernel_congr_onSphere hN μ J _ β hf T x hx
  have hπ : mixtureGibbsLaw μ β J =
      mixtureGibbsLaw μ β (literalFieldLift μ N (literalFieldMap μ N J)) :=
    gibbsLaw_congr_onSphere hN β hf
  unfold distance literalFieldDistance
  rw [hκ, hπ]
  unfold distance
  rfl

/-- The original Haar failure bound needs independence only from the
spherical Hamiltonian, even when the remaining tensor information depends
on the random initial probability. -/
private theorem independent_literal_initial_failure_le {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Ω → Disorder N μ.maxDegree) (ν : Ω → ProbabilityMeasure (Vector N))
    (hJ : HasLaw J (disorderLaw N μ.maxDegree) P) (hν : AEMeasurable ν P)
    (hind : IndepFun
      (fun ω => fun x : {x : Vector N // OnSphere x} =>
        field (mixtureCoefficients μ) (J ω) x) ν P)
    (hsphere : ∀ᵐ ω ∂P, ∀ᵐ x ∂(ν ω).toMeasure, OnSphere x)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | intervalDistance μ β T (J ω) (ν ω) < 1-ε} ≤
      ε⁻¹ * (∫ D, 1-distance μ β T D (uniformInitialProbability N)
        ∂disorderLaw N μ.maxDegree) := by
  let η : Measure (ProbabilityMeasure (Vector N)) := P.map ν
  have : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff hν).mpr inferInstance
  have hη : ∀ᵐ ξ ∂η, ∀ᵐ x ∂ξ.toMeasure, OnSphere x :=
    (ae_map_iff hν (sphericalInitialProbability_measurableSet N)).mpr hsphere
  let d : Measure (LiteralField μ N) :=
    (disorderLaw N μ.maxDegree).map (literalFieldMap μ N)
  have hmap : HasLaw (literalFieldMap μ N) d (disorderLaw N μ.maxDegree) :=
    hasLaw_map (literalFieldMap μ N).measurable.aemeasurable
  have hH := hmap.fun_comp hJ
  have hpair : HasLaw (fun ω => (literalFieldMap μ N (J ω), ν ω)) (d.prod η) P := by
    refine ⟨hH.aemeasurable.prodMk hν, ?_⟩
    rw [(literalFieldMap_indep P μ J ν hind).map_prod_eq_prod_map_map
      hH.aemeasurable hν, hH.map_eq]
  have hraw : HasLaw
      (fun p : Disorder N μ.maxDegree × ProbabilityMeasure (Vector N) =>
        (literalFieldMap μ N p.1, p.2))
      (d.prod η) ((disorderLaw N μ.maxDegree).prod η) := by
    refine ⟨((literalFieldMap μ N).measurable.prodMap measurable_id).aemeasurable, ?_⟩
    simpa only [Measure.map_id, Prod.map_def, id_eq, d] using
      (Measure.map_prod_map (disorderLaw N μ.maxDegree) η
        (literalFieldMap μ N).measurable measurable_id).symm
  have hE : MeasurableSet
      {p : LiteralField μ N × ProbabilityMeasure (Vector N) |
        literalFieldDistance μ β T p.1 p.2 < 1-ε} :=
    measurableSet_lt (literalFieldDistance_measurable hN μ β T) measurable_const
  have he : {ω | intervalDistance μ β T (J ω) (ν ω) < 1-ε} =ᵐ[P]
      {ω | literalFieldDistance μ β T (literalFieldMap μ N (J ω)) (ν ω) < 1-ε} := by
    filter_upwards [hsphere] with ω hω
    simp only [intervalDistance_eq_endpoint hN μ β T,
      literalFieldDistance_factorization hN μ β T (J ω) (ν ω) hω]
  have hsraw : ∀ᵐ p ∂(disorderLaw N μ.maxDegree).prod η,
      ∀ᵐ x ∂p.2.toMeasure, OnSphere x :=
    Measure.quasiMeasurePreserving_snd.ae hη
  have heraw :
      {p : Disorder N μ.maxDegree × ProbabilityMeasure (Vector N) |
        intervalDistance μ β T p.1 p.2 < 1-ε} =ᵐ[(disorderLaw N μ.maxDegree).prod η]
      {p | literalFieldDistance μ β T (literalFieldMap μ N p.1) p.2 < 1-ε} := by
    filter_upwards [hsraw] with p hp
    simp only [intervalDistance_eq_endpoint hN μ β T,
      literalFieldDistance_factorization hN μ β T p.1 p.2 hp]
  rw [measureReal_congr he, hpair.measureReal_eq hE,
    ← hraw.measureReal_eq hE, ← measureReal_congr heraw]
  exact independent_random_initial_failure_le hN μ β T η hη hε

/-- Source `(eq:intro-haar)`: every prescribed Borel spherical initial
probability has at most the uniform initial law's expected TV deficit in
the original finite-mixture Gaussian model, at every nonnegative time. -/
theorem finiteMixture_initial_meanDeficit_le_uniform {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x) :
    (∫ J, 1-distance μ β T J ν ∂disorderLaw N μ.maxDegree) ≤
      ∫ J, 1-distance μ β T J (uniformInitialProbability N)
        ∂disorderLaw N μ.maxDegree :=
  meanDeficit_le_uniform hN μ β T ν hν

/-- Source `thm:main-condensed` and `thm:main-initial`(i), with one common
positive exponent and the manuscript's literal independence from `H_N`
as a function on the sphere, rather than from its ambient polynomial or
raw Gaussian tensors. The literature hypotheses are exactly those of
`finiteMixture_main_condensed_and_initial_of_literature`. -/
theorem finiteMixture_main_condensed_and_initial_literal
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
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  obtain ⟨γ, hγ, hcondensed, hsep, hprescribed, _⟩ :=
    SourcePureAmplitudeScaling.finiteMixture_main_condensed_and_initial_of_literature
      μ h hChen hChenSen h5 h25 h24
  refine ⟨γ, hγ, hcondensed, hsep, hprescribed, ?_⟩
  intro Ω _ P _ J ν hJ hν hind hsphere ε hε
  apply squeeze_zero'
  · exact .of_forall fun N => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact independent_literal_initial_failure_le (P N) hN μ β
      (exponentialGridHorizon γ N) (J N) (ν N) (hJ N) (hν N)
      (hind N) (hsphere N hN) hε
  · simpa only [uniformMeanDeficit, mul_zero] using
      (uniformMeanDeficit_tendsto_zero μ β
        (fun N => exponentialGridHorizon γ N) hsep).const_mul ε⁻¹

end SlowEquilibration.SourceFiniteMixtureMainLiteral
