module
public import OverlapPaper.ReplicaSourceTerminal
public import OverlapPaper.ReplicaSourceGaussian

@[expose] public section

/-! Uniform boundedness of the actual terminal source difference, before
any Gaussian or branching integration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace OverlapPaper

theorem abs_replicaSourceTerminal_sub_le {d : ℕ} (J : Finset (Fin d))
    (θ : ℝ) (x : Fin d → ℝ) :
    |replicaSourceTerminal J θ x - replicaSourceTerminal J 0 x| ≤ |θ| := by
  let A : Configuration d → ℝ →L[ℝ] ℝ := fun ε =>
    replicaSpinProduct J ε • ContinuousLinearMap.id ℝ ℝ
  let b : Configuration d → ℝ := fun ε => ∑ l : Fin d, x l * spin (ε l)
  have hA (ε : Configuration d) : ‖A ε‖ ≤ 1 := by
    simp only [A, norm_smul, Real.norm_eq_abs, abs_replicaSpinProduct, one_smul, one_mul,
      ContinuousLinearMap.norm_id]
    norm_num
  have H := (finite_log_sum_exp_lipschitz A b 1 (by norm_num) hA).dist_le_mul θ 0
  simpa only [Real.dist_eq, replicaSourceTerminal, A, b, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Real.toNNReal_one, NNReal.coe_one,
    one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_comm, add_comm] using H

end OverlapPaper
