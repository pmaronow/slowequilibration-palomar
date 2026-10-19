module

public import SphericalAging.HamiltonianPicardDependence

public section

/-! Joint representatives preserve the actual predictable sigma algebra.
The actual trimmed L² isometry transfers the general measurable selector
back to ambient measure without postulating joint adaptedness.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.JointPredictableRepresentative
open HardSphereDynamics HamiltonianPicardDependence
variable {A Ω E : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- A jointly predictable representative of an actual strongly measurable
family of predictable L² classes, representing every parameter in the
ambient product time/sample measure. -/
theorem exists_joint_predictable_representative
    (f : A → lpMeas E ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P))
    (hf : StronglyMeasurable f) :
    ∃ G : A × (ℝ≥0 × Ω) → E,
      StronglyMeasurable[‹MeasurableSpace A›.prod F.predictable] G ∧ ∀ a,
        (fun z => G (a, z)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
          (f a : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let e := lpMeasToLpTrimLie E ℝ 2 (nonnegativeLebesgueMeasure.prod P) (predictable_le_prod F)
  have hsm : StronglyMeasurable (fun a => e (f a)) := e.continuous.comp_stronglyMeasurable hf
  obtain ⟨G, hG, hGa⟩ := @JointLpRepresentative.exists_joint_representative A (ℝ≥0 × Ω) E
    ‹MeasurableSpace A› F.predictable _ _ _ _ _ _
    ((nonnegativeLebesgueMeasure.prod P).trim (predictable_le_prod F)) (fun a => e (f a)) hsm
  refine ⟨G, hG, fun a => ?_⟩
  have hae : (fun z => G (a, z)) =ᵐ[nonnegativeLebesgueMeasure.prod P] (e (f a) : Lp E 2
      ((nonnegativeLebesgueMeasure.prod P).trim (predictable_le_prod F))) :=
    MeasureTheory.ae_eq_of_ae_eq_trim (hGa a)
  exact hae.trans (lpMeasToLpTrim_ae_eq (predictable_le_prod F) (f a))

variable {N p : ℕ} [IsProbabilityMeasure P]

/-- The actual Hamiltonian cutoff class has a jointly predictable version
on every bounded disorder set, simultaneously with initial-state parameters.
This is a constructed property of the genuine Picard classes. -/
theorem exists_joint_predictable_hamiltonianClass (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ) (hR : 0 < R) (B T : ℝ≥0) :
    ∃ G : (BoundedDisorder N p B × State N) × (ℝ≥0 × Ω) → State N,
      StronglyMeasurable[(inferInstance : MeasurableSpace (BoundedDisorder N p B × State N)).prod F.predictable] G ∧
      ∀ q, (fun z => G (q, z)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (hamiltonianClass D β R hR B T q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  obtain ⟨K, hK⟩ := hamiltonianClass_lipschitz (p := p) D β R hR B T
  exact exists_joint_predictable_representative _ hK.continuous.stronglyMeasurable

end SphericalAging.JointPredictableRepresentative
