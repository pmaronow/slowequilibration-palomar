-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalLocalizedCoefficientFamily
public import SlowEquilibration.SphericalWeightedJointRepresentatives
public import SlowEquilibration.SphericalZeroGibbsLaw

/-! Actual jointly continuous killed variational solutions on the common
uniform-sphere completed graph. Coercivity is derived from the positive
rate and actual exponential density; it is not supplied as a premise. -/
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

def jointKilledRho (β : ℝ) (H : Θ×Vector N→ℝ) (hH : Continuous H) : Θ→Vector N→ᵇℝ :=
  sphericalLocalizedFamily (fun z => Real.exp (β*H z)) (Real.continuous_exp.comp (hH.const_mul β))

def jointKilledSigma (β θ : ℝ) (H κ : Θ×Vector N→ℝ) (hH : Continuous H)
    (hκ : Continuous κ) : Θ→Vector N→ᵇℝ :=
  sphericalLocalizedFamily (fun z => (θ+κ z)*Real.exp (β*H z))
    ((continuous_const.add hκ).mul (Real.continuous_exp.comp (hH.const_mul β)))

def jointKilledForcing (β : ℝ) (H κ : Θ×Vector N→ℝ) (hH : Continuous H)
    (hκ : Continuous κ) (p : Θ) : Lp ℝ 2 (gibbsLaw N 0 (fun _ => 0)) :=
  let _ := gibbsLaw_zeroHamiltonian_probability N
  BoundedContinuousFunction.toLp 2 (gibbsLaw N 0 (fun _ => 0)) ℝ
    (sphericalLocalizedFamily (fun z => κ z*Real.exp (β*H z))
      (hκ.mul (Real.continuous_exp.comp (hH.const_mul β))) p)

theorem jointKilledForcing_continuous (β : ℝ) (H κ : Θ×Vector N→ℝ) (hH : Continuous H)
    (hκ : Continuous κ) : Continuous (jointKilledForcing β H κ hH hκ) := by
  let _ := gibbsLaw_zeroHamiltonian_probability N
  exact (BoundedContinuousFunction.toLp 2 (gibbsLaw N 0 (fun _ => 0)) ℝ).continuous.comp
    (sphericalLocalizedFamily_continuous _ _)

theorem jointKilledCoefficients_positive (hN : 1≤N) (β θ : ℝ) (hθ : 0<θ)
    (H κ : Θ×Vector N→ℝ) (hH : Continuous H) (hκ : Continuous κ) (hκ0 : ∀ z,0≤κ z)
    (p : Θ) : ∃ c : ℝ,0<c ∧
      (∀ᵐ x ∂gibbsLaw N 0 (fun _ => 0),c≤jointKilledRho β H hH p x) ∧
      ∀ᵐ x ∂gibbsLaw N 0 (fun _ => 0),c≤jointKilledSigma β θ H κ hH hκ p x := by
  obtain ⟨a,ha,har⟩ := sphericalLocalizedFamily_positive_lower hN 0 (fun _ => 0)
    (fun z => Real.exp (β*H z)) (Real.continuous_exp.comp (hH.const_mul β)) p (fun x => Real.exp_pos _)
  obtain ⟨b,hb,hbs⟩ := sphericalLocalizedFamily_positive_lower hN 0 (fun _ => 0)
    (fun z => (θ+κ z)*Real.exp (β*H z))
    ((continuous_const.add hκ).mul (Real.continuous_exp.comp (hH.const_mul β))) p
    (fun x => mul_pos (by linarith [hκ0 (p,x)]) (Real.exp_pos _))
  refine ⟨min a b,lt_min ha hb,har.mono (fun _ hx => (min_le_left _ _).trans hx),?_⟩
  exact hbs.mono (fun _ hx => (min_le_right _ _).trans hx)

def jointKilledSolution (hN : 1≤N) (β θ : ℝ) (H κ : Θ×Vector N→ℝ)
    (hH : Continuous H) (hκ : Continuous κ) (p : Θ) :
    sphericalSobolevGraph hN 0 (fun _ => 0) continuous_const :=
  sphericalWeightedSolution hN 0 (fun _ => 0) continuous_const
    (jointKilledRho β H hH p) (jointKilledSigma β θ H κ hH hκ p) (jointKilledForcing β H κ hH hκ p)

theorem jointKilledSolution_continuous (hN : 1≤N) (β θ : ℝ) (hθ : 0<θ)
    (H κ : Θ×Vector N→ℝ) (hH : Continuous H) (hκ : Continuous κ) (hκ0 : ∀ z,0≤κ z) :
    Continuous (jointKilledSolution hN β θ H κ hH hκ) :=
  sphericalWeightedSolution_continuous hN 0 (fun _ => 0) continuous_const _ _
    (sphericalLocalizedFamily_continuous _ _) (sphericalLocalizedFamily_continuous _ _)
    (jointKilledCoefficients_positive hN β θ hθ H κ hH hκ hκ0)
    _ (jointKilledForcing_continuous β H κ hH hκ)

theorem jointKilledSolution_joint_representatives
    [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (hN : 1≤N) (β θ : ℝ) (hθ : 0<θ)
    (H κ : Θ×Vector N→ℝ) (hH : Continuous H) (hκ : Continuous κ) (hκ0 : ∀ z,0≤κ z) :
    ∃ U : Θ×Vector N→ℝ,∃ G : (Fin N×Fin N)→Θ×Vector N→ℝ,
      StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
      (∀ p,(fun x => U (p,x))=ᵐ[gibbsLaw N 0 (fun _ => 0)]
        (jointKilledSolution hN β θ H κ hH hκ p).val.fst) ∧
      ∀ ij p,(fun x => G ij (p,x))=ᵐ[gibbsLaw N 0 (fun _ => 0)]
        (jointKilledSolution hN β θ H κ hH hκ p).val.snd ij :=
  sphericalWeightedSolution_joint_representatives hN 0 (fun _ => 0) continuous_const _ _
    (sphericalLocalizedFamily_continuous _ _) (sphericalLocalizedFamily_continuous _ _)
    (jointKilledCoefficients_positive hN β θ hθ H κ hH hκ hκ0)
    _ (jointKilledForcing_continuous β H κ hH hκ)

end SlowEquilibration.SphericalForm
