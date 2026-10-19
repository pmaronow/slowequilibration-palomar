-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CovarianceProfileOrders
public import SlowEquilibration.NormalizedObservationCoercivity

/-! The actual normalized score and tangent-gradient blocks, with literal
coefficient duals used in the two-point Gaussian density calculations. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression
open scoped RealInnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def normalizedScore {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt (N:ℝ))⁻¹ • scoreCLM c x

lemma normalizedScore_dual {N P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (u : EuclideanSpace ℝ (Fin 2)) :
    (innerSL ℝ u).comp (normalizedScore c x)=
      (u 0/Real.sqrt (N:ℝ)) • flatJetCLM c 0 x (fun i => Fin.elim0 i)+
      (u 1/Real.sqrt (N:ℝ)) • flatJetCLM c 1 x (fun _ => x) := by
  ext g
  simp only [normalizedScore,ContinuousLinearMap.comp_apply,add_apply,smul_apply,smul_eq_mul,
    innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.smul_apply]
  rw [Fin.sum_univ_two,scoreCLM_apply_zero,scoreCLM_apply_one]
  simp only [flatJetCLM_apply]
  ring

lemma gradientCLM_dual {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : EuclideanSpace ℝ (Fin m)) :
    (innerSL ℝ v).comp (gradientCLM c x e)=flatJetCLM c 1 x (fun _ => frameSum e v) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial,gradientCLM_apply,flatJetCLM_apply,jet_one_frameSum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

end
end SlowEquilibration.NormalizedPairObservations
