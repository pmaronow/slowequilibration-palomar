-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalFormCore
public import SlowEquilibration.BoundedContinuousL2Multiplication
public import SlowEquilibration.CoerciveOperatorContinuity
public import SlowEquilibration.WeightedCoordinateOperator

/-! A literal bounded-density variational operator on the actual completed
spherical gradient graph. Coercivity and inversion are proved from the
pointwise positive coefficients and the actual graph norm identity. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def sphericalGradientCoordinate (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ij : Fin N × Fin N) :
    sphericalSobolevGraph hN β H hH →L[ℝ] Lp ℝ 2 (gibbsLaw N β H) :=
  (PiLp.proj 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) ij).comp
    (sphericalEnergyGradientMap hN β H hH)

theorem sphericalGradientCoordinate_apply (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ij : Fin N × Fin N) (u : sphericalSobolevGraph hN β H hH) :
    sphericalGradientCoordinate hN β H hH ij u=u.val.snd ij := rfl

theorem sphericalValueCoordinate_apply (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (u : sphericalSobolevGraph hN β H hH) :
    sphericalEnergyL2Map hN β H hH u=u.val.fst := rfl

def sphericalGradientCoordinateAdjoint (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ij : Fin N × Fin N) :
    Lp ℝ 2 (gibbsLaw N β H) →L[ℝ] sphericalSobolevGraph hN β H hH :=
  ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=sphericalSobolevGraph hN β H hH)
    (F:=Lp ℝ 2 (gibbsLaw N β H)) (sphericalGradientCoordinate hN β H hH ij)

def sphericalWeightedOperator (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ρ σ : Vector N →ᵇ ℝ) :=
  WeightedCoordinateOperator.operator (E:=sphericalSobolevGraph hN β H hH)
    (F:=Lp ℝ 2 (gibbsLaw N β H)) (sphericalGradientCoordinate hN β H hH)
    (sphericalEnergyL2Map hN β H hH)
    (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) ρ)
    (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) σ)

theorem sphericalWeightedOperator_inner (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ρ σ : Vector N →ᵇ ℝ)
    (u v : sphericalSobolevGraph hN β H hH) :
    inner ℝ (sphericalWeightedOperator hN β H hH ρ σ u) v=
      (∑ ij : Fin N × Fin N,inner ℝ
        (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) ρ (u.val.snd ij)) (v.val.snd ij))+
      inner ℝ (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) σ u.val.fst) v.val.fst := by
  have hh := WeightedCoordinateOperator.operator_inner (E:=sphericalSobolevGraph hN β H hH)
    (F:=Lp ℝ 2 (gibbsLaw N β H)) (sphericalGradientCoordinate hN β H hH)
    (sphericalEnergyL2Map hN β H hH)
    (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) ρ)
    (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) σ) u v
  simpa only [sphericalWeightedOperator,sphericalGradientCoordinate_apply,sphericalValueCoordinate_apply] using hh

theorem sphericalWeightedOperator_coercive (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ρ σ : Vector N →ᵇ ℝ) (c : ℝ)
    (hρ : ∀ᵐ x ∂gibbsLaw N β H,c ≤ ρ x) (hσ : ∀ᵐ x ∂gibbsLaw N β H,c ≤ σ x)
    (u : sphericalSobolevGraph hN β H hH) :
    c*‖u‖^2 ≤ inner ℝ (sphericalWeightedOperator hN β H hH ρ σ u) u := by
  have hG : c*(∑ ij : Fin N × Fin N,‖u.val.snd ij‖^2) ≤
      ∑ ij : Fin N × Fin N,inner ℝ
        (BoundedContinuousL2Multiplication.operator (gibbsLaw N β H) ρ (u.val.snd ij)) (u.val.snd ij) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun ij _ => BoundedContinuousL2Multiplication.operator_inner_lower_bound
      (gibbsLaw N β H) ρ c hρ (u.val.snd ij))
  have hV := BoundedContinuousL2Multiplication.operator_inner_lower_bound
    (gibbsLaw N β H) σ c hσ u.val.fst
  have hn : ‖u‖^2=‖u.val.fst‖^2+∑ ij : Fin N × Fin N,‖u.val.snd ij‖^2 := by
    rw [sphericalSobolev_norm_sq,sphericalCompletedDirichlet,← real_inner_self_eq_norm_sq,
      PiLp.inner_apply]
    simp only [real_inner_self_eq_norm_sq]
    rfl
  rw [sphericalWeightedOperator_inner,hn]
  nlinarith

theorem sphericalWeightedOperator_continuous {Θ : Type*} [TopologicalSpace Θ]
    (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (ρ σ : Θ → Vector N →ᵇ ℝ) (hρ : Continuous ρ) (hσ : Continuous σ) :
    Continuous (fun p => sphericalWeightedOperator hN β H hH (ρ p) (σ p)) := by
  have hR := (BoundedContinuousL2Multiplication.operator_lipschitz (gibbsLaw N β H)).continuous.comp hρ
  have hS := (BoundedContinuousL2Multiplication.operator_lipschitz (gibbsLaw N β H)).continuous.comp hσ
  unfold sphericalWeightedOperator WeightedCoordinateOperator.operator
  apply Continuous.add
  · apply continuous_finsetSum
    intro ij _
    exact continuous_const.clm_comp (hR.clm_comp continuous_const)
  · exact continuous_const.clm_comp (hS.clm_comp continuous_const)

/-- Actual solution in the fixed completed graph, by the proved coercive
operator inverse. This definition supplies a common Hilbert parameter space. -/
def sphericalWeightedSolution (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ρ σ : Vector N →ᵇ ℝ) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    sphericalSobolevGraph hN β H hH :=
  Ring.inverse (sphericalWeightedOperator hN β H hH ρ σ)
    ((sphericalWeakSolution hN β H hH) f)

theorem sphericalWeightedSolution_equation (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (ρ σ : Vector N →ᵇ ℝ) (c : ℝ) (hc : 0 < c)
    (hρ : ∀ᵐ x ∂gibbsLaw N β H,c ≤ ρ x) (hσ : ∀ᵐ x ∂gibbsLaw N β H,c ≤ σ x)
    (f : Lp ℝ 2 (gibbsLaw N β H)) (v : sphericalSobolevGraph hN β H hH) :
    inner ℝ (sphericalWeightedOperator hN β H hH ρ σ (sphericalWeightedSolution hN β H hH ρ σ f)) v=
      inner ℝ f v.val.fst := by
  have he : sphericalWeightedOperator hN β H hH ρ σ
      (sphericalWeightedSolution hN β H hH ρ σ f)=sphericalWeakSolution hN β H hH f :=
    CoerciveOperatorContinuity.inverse_apply_equation (E:=sphericalSobolevGraph hN β H hH)
      (sphericalWeightedOperator hN β H hH ρ σ) c hc
      (sphericalWeightedOperator_coercive hN β H hH ρ σ c hρ hσ) (sphericalWeakSolution hN β H hH f)
  rw [he]
  exact (sphericalCompletedDirichlet_add_L2 hN β H hH (sphericalWeakSolution hN β H hH f) v).symm.trans
    (sphericalWeakSolution_spec hN β H hH f v)

theorem sphericalWeightedSolution_continuous {Θ : Type*} [TopologicalSpace Θ]
    (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (ρ σ : Θ → Vector N →ᵇ ℝ) (hρ : Continuous ρ) (hσ : Continuous σ)
    (hp : ∀ p,∃ c : ℝ,0<c ∧ (∀ᵐ x ∂gibbsLaw N β H,c ≤ ρ p x) ∧
      ∀ᵐ x ∂gibbsLaw N β H,c ≤ σ p x)
    (f : Θ → Lp ℝ 2 (gibbsLaw N β H)) (hf : Continuous f) :
    Continuous (fun p => sphericalWeightedSolution hN β H hH (ρ p) (σ p) (f p)) := by
  unfold sphericalWeightedSolution
  apply CoerciveOperatorContinuity.solution_continuous (E:=sphericalSobolevGraph hN β H hH)
    (fun p => sphericalWeightedOperator hN β H hH (ρ p) (σ p))
    (sphericalWeightedOperator_continuous hN β H hH ρ σ hρ hσ)
  · intro p
    obtain ⟨c,hc,hρp,hσp⟩ := hp p
    exact ⟨c,hc,sphericalWeightedOperator_coercive hN β H hH (ρ p) (σ p) c hρp hσp⟩
  · exact (sphericalWeakSolution hN β H hH).continuous.comp hf

end SlowEquilibration.SphericalForm
