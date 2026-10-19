-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeightedOperatorUniqueness
public import SlowEquilibration.SphericalGibbsTiltIdentity

/-! Exact weighted completed-form pairings under the literal Gibbs
density. The partition ratio stays exact throughout the transport. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem integral_exp_changeGibbs (hN : 1≤N) (β₀ β₁ : ℝ) (H₀ H₁ : Vector N→ℝ)
    (hH₀ : Continuous H₀) (hH₁ : Continuous H₁) (f : Vector N→ℝ) :
    (∫ x,Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*f x ∂gibbsLaw N β₀ H₀)=
      (partition N β₁ H₁/partition N β₀ H₀)*(∫ x,f x ∂gibbsLaw N β₁ H₁) := by
  have hM := div_pos (partition_pos hN β₁ hH₁) (partition_pos hN β₀ hH₀)
  have hw : Continuous (gibbsEnergyDifference β₀ β₁ H₀ H₁) :=
    (hH₁.const_mul β₁).sub (hH₀.const_mul β₀)
  have he := integral_normalizedTilt (gibbsLaw N β₀ H₀) _ hw.measurable hM f
  rw [← gibbsLaw_normalizedTilt hN β₀ β₁ H₀ H₁ hH₀ hH₁] at he
  exact ((div_eq_iff (ne_of_gt hM)).mp he.symm).trans (mul_comm _ _)

theorem sphericalWeightedOperator_changeGibbs (hN : 1≤N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N→ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (ρ σ : Vector N→ᵇℝ) (q : Vector N→ℝ)
    (hρ : ρ=ᵐ[gibbsLaw N β₀ H₀] fun x => Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x))
    (hσ : σ=ᵐ[gibbsLaw N β₀ H₀] fun x => q x*Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x))
    (u₀ v₀ : sphericalSobolevGraph hN β₀ H₀ hH₀)
    (u₁ v₁ : sphericalSobolevGraph hN β₁ H₁ hH₁)
    (hu : u₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] u₀.val.fst)
    (hv : v₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] v₀.val.fst)
    (hGu : ∀ ij : Fin N×Fin N,u₁.val.snd ij=ᵐ[gibbsLaw N β₁ H₁] u₀.val.snd ij)
    (hGv : ∀ ij : Fin N×Fin N,v₁.val.snd ij=ᵐ[gibbsLaw N β₁ H₁] v₀.val.snd ij) :
    inner ℝ (sphericalWeightedOperator hN β₀ H₀ hH₀ ρ σ u₀) v₀=
      (partition N β₁ H₁/partition N β₀ H₀)*
        (sphericalCompletedDirichlet hN β₁ H₁ hH₁ u₁ v₁+
          ∫ x,q x*u₁.val.fst x*v₁.val.fst x ∂gibbsLaw N β₁ H₁) := by
  let M := partition N β₁ H₁/partition N β₀ H₀
  have hgrad (ij : Fin N×Fin N) :
      (∫ x,ρ x*u₀.val.snd ij x*v₀.val.snd ij x ∂gibbsLaw N β₀ H₀)=
      M*(∫ x,u₁.val.snd ij x*v₁.val.snd ij x ∂gibbsLaw N β₁ H₁) := by
    calc
      _ = ∫ x,Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*
          (u₀.val.snd ij x*v₀.val.snd ij x) ∂gibbsLaw N β₀ H₀ := by
        apply integral_congr_ae
        filter_upwards [hρ] with x hx
        rw [hx,mul_assoc]
      _ = M*(∫ x,u₀.val.snd ij x*v₀.val.snd ij x ∂gibbsLaw N β₁ H₁) :=
        integral_exp_changeGibbs hN β₀ β₁ H₀ H₁ hH₀ hH₁ _
      _ = M*(∫ x,u₁.val.snd ij x*v₁.val.snd ij x ∂gibbsLaw N β₁ H₁) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hGu ij,hGv ij] with x hux hvx
        rw [hux,hvx]
  have hval : (∫ x,σ x*u₀.val.fst x*v₀.val.fst x ∂gibbsLaw N β₀ H₀)=
      M*(∫ x,q x*u₁.val.fst x*v₁.val.fst x ∂gibbsLaw N β₁ H₁) := by
    calc
      _ = ∫ x,Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*
          (q x*u₀.val.fst x*v₀.val.fst x) ∂gibbsLaw N β₀ H₀ := by
        apply integral_congr_ae
        filter_upwards [hσ] with x hx
        rw [hx]
        ring
      _ = M*(∫ x,q x*u₀.val.fst x*v₀.val.fst x ∂gibbsLaw N β₁ H₁) :=
        integral_exp_changeGibbs hN β₀ β₁ H₀ H₁ hH₀ hH₁ _
      _ = M*(∫ x,q x*u₁.val.fst x*v₁.val.fst x ∂gibbsLaw N β₁ H₁) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hu,hv] with x hux hvx
        rw [hux,hvx]
  rw [sphericalWeightedOperator_integral]
  simp_rw [hgrad]
  rw [hval,← Finset.mul_sum,← mul_add]
  congr 1
  change _=inner ℝ u₁.val.snd v₁.val.snd+_
  rw [PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun x => by simp only [RCLike.inner_apply,conj_trivial,mul_comm])

end SlowEquilibration.SphericalForm
