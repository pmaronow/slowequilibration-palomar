module
public import QuantitativePaper.LogJetBounds

@[expose] public section

/-! Smoothness and globally bounded positive-order jets of a finite log-sum
of exponentials of genuine continuous linear functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [Nonempty ι]

def finiteLinearPartition (l : ι → E →L[ℝ] ℝ) (x : E) : ℝ := ∑ i,Real.exp (l i x)
def finiteLinearSoftmax (l : ι → E →L[ℝ] ℝ) (x : E) : ℝ := Real.log (finiteLinearPartition l x)

theorem finiteLinearPartition_pos (l : ι → E →L[ℝ] ℝ) (x : E) : 0 < finiteLinearPartition l x :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem contDiff_finiteLinearPartition (l : ι → E →L[ℝ] ℝ) (N : ℕ) :
    ContDiff ℝ N (finiteLinearPartition l) := by
  exact ContDiff.sum (fun i _ => (l i).contDiff.exp)

theorem contDiff_finiteLinearSoftmax (l : ι → E →L[ℝ] ℝ) (N : ℕ) :
    ContDiff ℝ N (finiteLinearSoftmax l) :=
  (contDiff_finiteLinearPartition l N).log (fun x => (finiteLinearPartition_pos l x).ne')

theorem norm_iteratedFDeriv_linear_le {j : ℕ} (l : E →L[ℝ] ℝ) (D : ℝ)
    (hD : 1 ≤ D) (hl : ‖l‖ ≤ D) (hj : 1 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j l x‖ ≤ D^j := by
  have he : fderiv ℝ (l : E → ℝ) = fun _ => l := funext fun x => l.hasFDerivAt.fderiv
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 1 (l : E → ℝ) x‖ ≤ D^1
      simpa only [norm_iteratedFDeriv_one,he,pow_one] using hl
    | succ j =>
      rw [←norm_iteratedFDeriv_fderiv,he,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]
      positivity

def finiteLinearNormBound (l : ι → E →L[ℝ] ℝ) : ℝ := max 1 (∑ i,‖l i‖)

theorem norm_iteratedFDeriv_finiteLinearPartition_le (l : ι → E →L[ℝ] ℝ)
    (N j : ℕ) (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (finiteLinearPartition l) x‖ ≤
      (j.factorial : ℝ)*(finiteLinearNormBound l)^j*finiteLinearPartition l x := by
  have hD : 1 ≤ finiteLinearNormBound l := le_max_left _ _
  have hl (i : ι) : ‖l i‖ ≤ finiteLinearNormBound l :=
    (Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ i)).trans (le_max_right _ _)
  unfold finiteLinearPartition
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((l i).contDiff.exp : ContDiff ℝ j _).contDiffAt)]
  apply (norm_sum_le _ _).trans
  have hh (i : ι) : ‖iteratedFDeriv ℝ j (fun y => Real.exp (l i y)) x‖ ≤
      (j.factorial : ℝ)*(finiteLinearNormBound l)^j*Real.exp (l i x) := by
    have hb := norm_iteratedFDeriv_exp_mul_le (l i) (l i).contDiff hj 1 (finiteLinearNormBound l) x
      (fun r hr hrj => norm_iteratedFDeriv_linear_le (l i) _ hD (hl i) hr x)
    simpa only [one_mul,abs_one,max_self,one_pow,mul_one,mul_assoc,mul_left_comm,mul_comm] using hb
  exact (Finset.sum_le_sum fun i _ => hh i).trans_eq (Finset.mul_sum _ _ _).symm

def finitePartitionPowerBound (l : ι → E →L[ℝ] ℝ) (N : ℕ) : ℝ :=
  max 1 (∑ j ∈ Finset.range (N+1),|(j.factorial : ℝ)*(finiteLinearNormBound l)^j|)

theorem finitePartitionCoefficient_le_power (l : ι → E →L[ℝ] ℝ) (N i : ℕ)
    (hi0 : 1 ≤ i) (hi : i ≤ N) :
    (i.factorial : ℝ)*(finiteLinearNormBound l)^i ≤ (finitePartitionPowerBound l N)^i := by
  have hh : |(i.factorial : ℝ)*(finiteLinearNormBound l)^i| ≤
      ∑ j ∈ Finset.range (N+1),|(j.factorial : ℝ)*(finiteLinearNormBound l)^j| :=
    Finset.single_le_sum (f := fun j => |(j.factorial : ℝ)*(finiteLinearNormBound l)^j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  exact (le_abs_self _).trans (hh.trans ((le_max_right _ _).trans
    (le_self_pow₀ (show 1 ≤ finitePartitionPowerBound l N from le_max_left _ _) (by omega))))

theorem norm_iteratedFDeriv_finiteLinearSoftmax_le (l : ι → E →L[ℝ] ℝ)
    (N j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (finiteLinearSoftmax l) x‖ ≤
      (j.factorial : ℝ)*logJetCoefficient j*(finitePartitionPowerBound l N)^j := by
  apply norm_iteratedFDeriv_log_le_of_relative (finiteLinearPartition l)
    (contDiff_finiteLinearPartition l N) (finiteLinearPartition_pos l) hj0 hj _ x
  intro i hi hij
  exact (norm_iteratedFDeriv_finiteLinearPartition_le l N i (hij.trans hj) x).trans
    (mul_le_mul_of_nonneg_right (finitePartitionCoefficient_le_power l N i hi (hij.trans hj))
      (finiteLinearPartition_pos l x).le)

end QuantitativePaper
