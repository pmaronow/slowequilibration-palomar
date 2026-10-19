-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceZeroDefectAnyRepresentatives
public import SlowEquilibration.ConditionedEntranceWeightedEnergyJointAbsorption

/-! The same frozen-axis reference representative controls both
commutators in a global raw weighted-energy inequality. A single
second axis moment yields the manuscript's final energy absorption. -/
@[expose] public section
noncomputable section
open MeasureTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem axisGibbs_weighted_energy_absorption_of_second_moment
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (w : Vector N×Vector N → ℝ) (hw : Continuous w)
    (M : ℝ) (hM : 1/2 ≤ M)
    (F U : Vector N×Vector N → ℝ)
    (GF G : (Fin N×Fin N) → Vector N×Vector N → ℝ)
    (hFm : Measurable F) (hUm : Measurable U)
    (hGFm : ∀ ij, Measurable (GF ij)) (hGm : ∀ ij, Measurable (G ij))
    (hFrozenF : ∀ u v x, F (u,x)=F (v,x))
    (hFrozenGF : ∀ ij u v x, GF ij (u,x)=GF ij (v,x))
    (F₀ : sphericalSobolevGraph hN β H₀ hH₀)
    (hFrep : (fun x => F (0,x)) =ᵐ[gibbsLaw N β H₀] F₀.val.fst)
    (hGFrep : ∀ ij, (fun x => GF ij (0,x)) =ᵐ[gibbsLaw N β H₀] F₀.val.snd ij)
    (hF₀lo : ∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F₀.val.fst x)
    (hFmass : (∫ x, F (0,x) ∂gibbsLaw N β H₀) = 2)
    (ν : Measure (Vector N×Vector N))
    (hν : ν = normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M)
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1)
    (hKint : Integrable (fun z => (tiltDefect w z)^2*(F z-1)) ν)
    (hJint : Integrable (fun z => (tiltDefect w z)^2*
      (∑ ij : Fin N×Fin N,(GF ij z)^2/F z)) ν)
    (hAint : Integrable (fun z => F z*U z^2) ν)
    (hBint : Integrable (fun z => F z*
      (∑ ij : Fin N×Fin N,(G ij z)^2)) ν)
    (lam ε H R : ℝ) (hlam : 0 < lam) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hεaxis : ∀ᵐ x ∂gibbsLaw N β H₀,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2
        ∂sphereLaw N) ≤ ε)
    (hFisher : sphericalFisher hN β H₀ hH₀ F₀ ≤ lam*H)
    (hraw :
      (∫ z, F z*(∑ ij : Fin N×Fin N,(G ij z)^2) ∂ν)+
        lam/2*(∫ z, F z*U z^2 ∂ν) ≤
        lam*R+lam/2*
          |∫ z, tiltDefect w z*(F z-1)*U z^2 ∂ν|+
          |∫ z, tiltDefect w z*U z*
            (∑ ij : Fin N×Fin N, GF ij z*G ij z) ∂ν|) :
    (∫ z, F z*(∑ ij : Fin N×Fin N,(G ij z)^2) ∂ν)/lam ≤
      2*R+ε+2*ε*H := by
  let : IsProbabilityMeasure (gibbsLaw N β H₀) :=
    gibbsLaw_probability hN β hH₀
  have hFint : Integrable (fun x => F (0,x)) (gibbsLaw N β H₀) :=
    ((Lp.memLp F₀.val.fst).integrable (by norm_num)).congr hFrep.symm
  have hF0lo : ∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F (0,x) := by
    filter_upwards [hFrep,hF₀lo] with x hf hlo
    rw [hf]
    exact hlo
  have hKsmall : (∫ z, (tiltDefect w z)^2*(F z-1) ∂ν) ≤ 2*ε := by
    rw [hν]
    exact zero_defect_projection_any_frozen_representative hN β H₀ hH₀
      w hw M hM F hFrozenF hFint hF0lo hFmass hε hεaxis
  have hJsmall : (∫ z, (tiltDefect w z)^2*
      (∑ ij : Fin N×Fin N,(GF ij z)^2/F z) ∂ν) ≤
        2*ε*sphericalFisher hN β H₀ hH₀ F₀ := by
    rw [hν]
    exact fisher_defect_projection_any_frozen_representatives hN β H₀ hH₀
      w hw M hM F GF hFrozenF hFrozenGF F₀ hFrep hGFrep hF₀lo hε hεaxis
  have hkm : Measurable (tiltDefect w) := by
    unfold tiltDefect
    fun_prop
  exact weighted_energy_absorption_of_integral_moments ν
    (tiltDefect w) F U GF G hkm hFm hUm hGFm hGm hFlo hUb
    hKint hJint hAint hBint hlam hε hH
    (sphericalFisher_nonnegative hN β H₀ hH₀ F₀ hF₀lo)
    hKsmall hJsmall hFisher hraw

end SlowEquilibration.ConditionedEntrance
