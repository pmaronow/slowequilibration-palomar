-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSignedCounts

/-! Finite Jordan decompositions for actual signed posterior integrals. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal
noncomputable section

/-- Bounded signed marks can be subtracted inside a posterior only after
absolute integrability of the nonnegative determinant factor has been proved. -/
theorem weighted_posterior_integrable_parts {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (D psi : Ω → ℝ) (hD : Integrable D ν) (hD0 : ∀ w, 0 ≤ D w)
    (hpsi : Measurable psi) (M : ℝ) (hbound : ∀ w, |psi w| ≤ M) :
    Integrable (fun w => D w * psi w) ν ∧
    (∫⁻ w, ENNReal.ofReal (D w) * ENNReal.ofReal (psi w) ∂ν) < ⊤ ∧
    (∫⁻ w, ENNReal.ofReal (D w) * ENNReal.ofReal (-psi w) ∂ν) < ⊤ ∧
    (∫ w, D w * psi w ∂ν) =
      (∫⁻ w, ENNReal.ofReal (D w) * ENNReal.ofReal (psi w) ∂ν).toReal -
      (∫⁻ w, ENNReal.ofReal (D w) * ENNReal.ofReal (-psi w) ∂ν).toReal := by
  have hi := hD.mul_bdd hpsi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => show ‖psi w‖ ≤ M by simpa only [Real.norm_eq_abs] using hbound w))
  have hp : (fun w => ENNReal.ofReal (D w * psi w)) =
      (fun w => ENNReal.ofReal (D w) * ENNReal.ofReal (psi w)) :=
    funext (fun w => ENNReal.ofReal_mul (hD0 w))
  have hn : (fun w => ENNReal.ofReal (-(D w * psi w))) =
      (fun w => ENNReal.ofReal (D w) * ENNReal.ofReal (-psi w)) := by
    funext w
    rw [neg_mul_eq_mul_neg, ENNReal.ofReal_mul (hD0 w)]
  refine ⟨hi, ?_, ?_, ?_⟩
  · rw [← hp]
    exact hi.lintegral_lt_top
  · rw [← hn]
    exact hi.neg.lintegral_lt_top
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, hp, hn]

lemma integrable_toReal_sub_integral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f g : Ω → ℝ≥0∞)
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν)
    (hfi : (∫⁻ w, f w ∂ν) < ⊤) (hgi : (∫⁻ w, g w ∂ν) < ⊤) :
    Integrable (fun w => (f w).toReal - (g w).toReal) ν ∧
    (∫ w, (f w).toReal - (g w).toReal ∂ν) =
      (∫⁻ w, f w ∂ν).toReal - (∫⁻ w, g w ∂ν).toReal := by
  have hif := integrable_toReal_of_lintegral_ne_top hf hfi.ne
  have hig := integrable_toReal_of_lintegral_ne_top hg hgi.ne
  exact ⟨hif.sub hig, by rw [integral_sub hif hig,
    integral_toReal hf (ae_lt_top' hf hfi.ne), integral_toReal hg (ae_lt_top' hg hgi.ne)]⟩

end
end SlowEquilibration.SphericalMarkedWindows
