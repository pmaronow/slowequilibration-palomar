-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeightedVariationalOperator
public import SphericalAging.JointLpRepresentative

/-! Joint value and actual completed normalized-gradient representatives
of the derived continuous common-domain spherical variational solutions. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

/-- Joint representatives are constructed from actual continuous solution
classes. No joint-gradient representative or measurability conclusion is
supplied as a premise. Every deterministic parameter slice is identified. -/
theorem sphericalWeightedSolution_joint_representatives {Θ : Type*}
    [TopologicalSpace Θ] [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (ρ σ : Θ → Vector N →ᵇ ℝ) (hρ : Continuous ρ) (hσ : Continuous σ)
    (hp : ∀ p,∃ c : ℝ,0<c ∧ (∀ᵐ x ∂gibbsLaw N β H,c ≤ ρ p x) ∧
      ∀ᵐ x ∂gibbsLaw N β H,c ≤ σ p x)
    (f : Θ → Lp ℝ 2 (gibbsLaw N β H)) (hf : Continuous f) :
    ∃ U : Θ × Vector N → ℝ,∃ G : (Fin N × Fin N) → Θ × Vector N → ℝ,
      StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
      (∀ p,(fun x => U (p,x))=ᵐ[gibbsLaw N β H]
        (sphericalWeightedSolution hN β H hH (ρ p) (σ p) (f p)).val.fst) ∧
      ∀ ij p,(fun x => G ij (p,x))=ᵐ[gibbsLaw N β H]
        (sphericalWeightedSolution hN β H hH (ρ p) (σ p) (f p)).val.snd ij := by
  have hs := sphericalWeightedSolution_continuous hN β H hH ρ σ hρ hσ hp f hf
  obtain ⟨U,hU,hUa⟩ := SphericalAging.JointLpRepresentative.exists_joint_representative
    (fun p => sphericalEnergyL2Map hN β H hH
      (sphericalWeightedSolution hN β H hH (ρ p) (σ p) (f p)))
    ((sphericalEnergyL2Map hN β H hH).continuous.comp hs).stronglyMeasurable
  have hg (ij : Fin N × Fin N) := SphericalAging.JointLpRepresentative.exists_joint_representative
    (fun p => sphericalGradientCoordinate hN β H hH ij
      (sphericalWeightedSolution hN β H hH (ρ p) (σ p) (f p)))
    ((sphericalGradientCoordinate hN β H hH ij).continuous.comp hs).stronglyMeasurable
  choose G hG hGa using hg
  exact ⟨U,G,hU,hG,hUa,hGa⟩

end SlowEquilibration.SphericalForm
