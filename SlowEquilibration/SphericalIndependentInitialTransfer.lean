module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalHaarTransferAsymptotics
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! # Initial laws independent of the field on an arbitrary sample space

The product-law Haar transfer is transported to a pair of genuinely
independent random variables. The actual tensor field law is retained.
-/
namespace SlowEquilibration.SphericalOrthogonalHaar
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1800000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

lemma sphericalInitialProbability_measurableSet (N : ℕ) :
    MeasurableSet {ν : ProbabilityMeasure (Vector N) | ∀ᵐ x ∂ν.toMeasure, OnSphere x} := by
  have he : {ν : ProbabilityMeasure (Vector N) | ∀ᵐ x ∂ν.toMeasure, OnSphere x}=
      {ν | ν.toMeasure {x | ¬OnSphere x}=0} := by
    ext ν
    change (∀ᵐ x ∂ν.toMeasure, OnSphere x) ↔ ν.toMeasure {x | ¬OnSphere x}=0
    rw [ae_iff]
  rw [he]
  exact measurableSet_eq_fun
    ((Measure.measurable_coe (sphere_measurableSet N).compl).comp measurable_subtype_coe)
    measurable_const

/-- The finite-dimensional source bound for an arbitrary independently
sampled initial probability. Independence gives the product law here; it
is not inserted as a replacement kernel or covariance assumption. -/
theorem independent_sampled_initial_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Ω → Disorder N μ.maxDegree)
    (ν : Ω → ProbabilityMeasure (Vector N))
    (hJ : HasLaw J (disorderLaw N μ.maxDegree) P)
    (hν : AEMeasurable ν P) (hind : IndepFun J ν P)
    (hsphere : ∀ᵐ ω ∂P, ∀ᵐ x ∂(ν ω).toMeasure, OnSphere x)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | intervalDistance μ β T (J ω) (ν ω)<1-ε} ≤
      ε⁻¹*(∫ D, 1-distance μ β T D (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree) := by
  let η : Measure (ProbabilityMeasure (Vector N)) := P.map ν
  have : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff hν).mpr inferInstance
  have hη : ∀ᵐ ξ ∂η, ∀ᵐ x ∂ξ.toMeasure, OnSphere x :=
    (ae_map_iff hν (sphericalInitialProbability_measurableSet N)).mpr hsphere
  have hpair : HasLaw (fun ω => (J ω,ν ω)) ((disorderLaw N μ.maxDegree).prod η) P := by
    refine ⟨hJ.aemeasurable.prodMk hν,?_⟩
    rw [hind.map_prod_eq_prod_map_map hJ.aemeasurable hν,hJ.map_eq]
  have hE : MeasurableSet {p : Disorder N μ.maxDegree × ProbabilityMeasure (Vector N) |
      intervalDistance μ β T p.1 p.2 < 1-ε} := by
    simp_rw [intervalDistance_eq_endpoint hN μ β T]
    exact measurableSet_lt (distance_joint_measurable hN μ β T) measurable_const
  rw [hpair.measureReal_eq hE]
  exact independent_random_initial_failure_le hN μ β T η hη hε

/-- The final random-initial-law convergence clause of red-haar on any
dimension-dependent probability spaces, with actual statistical
independence from the mixed tensor field. -/
theorem independent_sampled_initial_failure_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (hsep : uniformSeparationInProbability μ β T)
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (J : ∀ N, Ω N → Disorder N μ.maxDegree)
    (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N))
    (hJ : ∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N))
    (hν : ∀ N, AEMeasurable (ν N) (P N))
    (hind : ∀ N, IndepFun (J N) (ν N) (P N))
    (hsphere : ∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ x ∂(ν N ω).toMeasure, OnSphere x)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => (P N).real
      {ω | intervalDistance μ β (T N) (J N ω) (ν N ω)<1-ε}) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact .of_forall fun N => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact independent_sampled_initial_failure_le (P N) hN μ β (T N)
      (J N) (ν N) (hJ N) (hν N) (hind N) (hsphere N hN) hε
  · simpa only [uniformMeanDeficit,mul_zero] using
      (uniformMeanDeficit_tendsto_zero μ β T hsep).const_mul ε⁻¹

end
end SlowEquilibration.SphericalOrthogonalHaar
