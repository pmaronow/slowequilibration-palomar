-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalJointKilledVariational

/-! Actual common-domain killed variational resolvents with arbitrary
jointly continuous endpoint forcing, and literal coefficient values. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ]

theorem jointKilledRho_ae (hN : 1≤N) (β : ℝ) (H : Θ×Vector N→ℝ) (hH : Continuous H) (p : Θ) :
    jointKilledRho β H hH p=ᵐ[gibbsLaw N 0 (fun _ => 0)] fun x => Real.exp (β*H (p,x)) :=
  sphericalLocalizedFamily_ae hN 0 (fun _ => 0) _ _ p

theorem jointKilledSigma_ae (hN : 1≤N) (β θ : ℝ) (H κ : Θ×Vector N→ℝ)
    (hH : Continuous H) (hκ : Continuous κ) (p : Θ) :
    jointKilledSigma β θ H κ hH hκ p=ᵐ[gibbsLaw N 0 (fun _ => 0)]
      fun x => (θ+κ (p,x))*Real.exp (β*H (p,x)) :=
  sphericalLocalizedFamily_ae hN 0 (fun _ => 0) _ _ p

theorem jointKilledForcing_ae (hN : 1≤N) (β : ℝ) (H g : Θ×Vector N→ℝ)
    (hH : Continuous H) (hg : Continuous g) (p : Θ) :
    jointKilledForcing β H g hH hg p=ᵐ[gibbsLaw N 0 (fun _ => 0)]
      fun x => g (p,x)*Real.exp (β*H (p,x)) := by
  let := gibbsLaw_zeroHamiltonian_probability N
  exact (BoundedContinuousFunction.coeFn_toLp 2 (gibbsLaw N 0 (fun _ => 0)) ℝ
    (sphericalLocalizedFamily (fun z => g z*Real.exp (β*H z))
      (hg.mul (Real.continuous_exp.comp (hH.const_mul β))) p)).trans
    (sphericalLocalizedFamily_ae hN 0 (fun _ => 0) _ _ p)

def jointResolventSolution (hN : 1≤N) (β θ : ℝ) (H κ g : Θ×Vector N→ℝ)
    (hH : Continuous H) (hκ : Continuous κ) (hg : Continuous g) (p : Θ) :
    sphericalSobolevGraph hN 0 (fun _ => 0) continuous_const :=
  sphericalWeightedSolution hN 0 (fun _ => 0) continuous_const
    (jointKilledRho β H hH p) (jointKilledSigma β θ H κ hH hκ p) (jointKilledForcing β H g hH hg p)

theorem jointResolventSolution_continuous (hN : 1≤N) (β θ : ℝ) (hθ : 0<θ)
    (H κ g : Θ×Vector N→ℝ) (hH : Continuous H) (hκ : Continuous κ) (hg : Continuous g)
    (hκ0 : ∀ z,0≤κ z) : Continuous (jointResolventSolution hN β θ H κ g hH hκ hg) :=
  sphericalWeightedSolution_continuous hN 0 (fun _ => 0) continuous_const _ _
    (sphericalLocalizedFamily_continuous _ _) (sphericalLocalizedFamily_continuous _ _)
    (jointKilledCoefficients_positive hN β θ hθ H κ hH hκ hκ0)
    _ (jointKilledForcing_continuous β H g hH hg)

theorem jointResolventSolution_joint_representatives
    [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (hN : 1≤N) (β θ : ℝ) (hθ : 0<θ)
    (H κ g : Θ×Vector N→ℝ) (hH : Continuous H) (hκ : Continuous κ) (hg : Continuous g)
    (hκ0 : ∀ z,0≤κ z) :
    ∃ U : Θ×Vector N→ℝ,∃ G : (Fin N×Fin N)→Θ×Vector N→ℝ,
      StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
      (∀ p,(fun x => U (p,x))=ᵐ[gibbsLaw N 0 (fun _ => 0)]
        (jointResolventSolution hN β θ H κ g hH hκ hg p).val.fst) ∧
      ∀ ij p,(fun x => G ij (p,x))=ᵐ[gibbsLaw N 0 (fun _ => 0)]
        (jointResolventSolution hN β θ H κ g hH hκ hg p).val.snd ij :=
  sphericalWeightedSolution_joint_representatives hN 0 (fun _ => 0) continuous_const _ _
    (sphericalLocalizedFamily_continuous _ _) (sphericalLocalizedFamily_continuous _ _)
    (jointKilledCoefficients_positive hN β θ hθ H κ hH hκ hκ0)
    _ (jointKilledForcing_continuous β H g hH hg)

end SlowEquilibration.SphericalForm
