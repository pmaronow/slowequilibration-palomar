-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalJointGibbsKernel
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! Joint measurability of the literal completed-coordinate energy,
square-test generator and Gibbs-defect integrals. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]

def jointGibbsWeightedGradientSquare (β : ℝ) (H F : Θ×Vector N→ℝ)
    (G : (Fin N×Fin N)→Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∑ ij : Fin N×Fin N,∫ x,F (p,x)*(G ij (p,x))^2 ∂gibbsLaw N β (fun y => H (p,y))

def jointGibbsWeightedSquare (β : ℝ) (H F U : Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∫ x,F (p,x)*(U (p,x))^2 ∂gibbsLaw N β (fun y => H (p,y))

def jointGibbsKilledWeightedSquare (β : ℝ) (H κ F U : Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∫ x,κ (p,x)*F (p,x)*(U (p,x))^2 ∂gibbsLaw N β (fun y => H (p,y))

def jointGibbsKilledReference (β : ℝ) (H κ F : Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∫ x,κ (p,x)*F (p,x) ∂gibbsLaw N β (fun y => H (p,y))

def jointGibbsGeneratorSquare (β : ℝ) (H w L U : Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∫ x,Real.exp (-w (p,x))*L (p,x)*(U (p,x))^2 ∂gibbsLaw N β (fun y => H (p,y))

def jointGibbsTiltGradientCross (β : ℝ) (H w U : Θ×Vector N→ℝ)
    (GF G : (Fin N×Fin N)→Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∫ x,(1-Real.exp (-w (p,x)))*(∑ ij : Fin N×Fin N,U (p,x)*GF ij (p,x)*G ij (p,x))
    ∂gibbsLaw N β (fun y => H (p,y))

def jointGibbsFisher (β : ℝ) (H F : Θ×Vector N→ℝ)
    (G : (Fin N×Fin N)→Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∑ ij : Fin N×Fin N,∫ x,(G ij (p,x))^2/F (p,x) ∂gibbsLaw N β (fun y => H (p,y))

theorem jointGibbsEnergyIntegrals_measurable (hN : 1≤N) (β : ℝ)
    (H κ w L F U : Θ×Vector N→ℝ) (hH : Continuous H)
    (hκ : StronglyMeasurable κ) (hw : StronglyMeasurable w) (hL : StronglyMeasurable L)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (GF G : (Fin N×Fin N)→Θ×Vector N→ℝ)
    (hGF : ∀ ij,StronglyMeasurable (GF ij)) (hG : ∀ ij,StronglyMeasurable (G ij)) :
    Measurable (jointGibbsWeightedGradientSquare β H F G) ∧
    Measurable (jointGibbsWeightedSquare β H F U) ∧
    Measurable (jointGibbsKilledWeightedSquare β H κ F U) ∧
    Measurable (jointGibbsKilledReference β H κ F) ∧
    Measurable (jointGibbsGeneratorSquare β H w L U) ∧
    Measurable (jointGibbsTiltGradientCross β H w U GF G) ∧
    Measurable (jointGibbsFisher β H F GF) := by
  have he : StronglyMeasurable (fun z => Real.exp (-w z)) :=
    Real.continuous_exp.comp_stronglyMeasurable hw.neg
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact Finset.measurable_sum _ (fun ij _ => jointHamiltonian_integral_measurable hN β H hH
      (fun z => F z*(G ij z)^2) (hF.mul ((hG ij).pow 2)))
  · exact jointHamiltonian_integral_measurable hN β H hH _ (hF.mul (hU.pow 2))
  · exact jointHamiltonian_integral_measurable hN β H hH _ ((hκ.mul hF).mul (hU.pow 2))
  · exact jointHamiltonian_integral_measurable hN β H hH _ (hκ.mul hF)
  · exact jointHamiltonian_integral_measurable hN β H hH _ ((he.mul hL).mul (hU.pow 2))
  · exact jointHamiltonian_integral_measurable hN β H hH _
      ((stronglyMeasurable_const.sub he).mul
        (Finset.stronglyMeasurable_fun_sum _ (fun ij _ => (hU.mul (hGF ij)).mul (hG ij))))
  · exact Finset.measurable_sum _ (fun ij _ => jointHamiltonian_integral_measurable hN β H hH
      (fun z => (GF ij z)^2/F z) (((hGF ij).pow 2).div hF))

end SlowEquilibration.SphericalForm
