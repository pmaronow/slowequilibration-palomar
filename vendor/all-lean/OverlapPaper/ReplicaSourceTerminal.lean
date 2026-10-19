module
public import OverlapPaper.ReplicaSourceDefinitions
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Exact counting-measure factorization of the replica spin-product source.
All unmarked replica coordinates are summed, including empty source products. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000

theorem sum_configuration_prod {d : ℕ} (f : Fin d → Bool → ℝ) :
    (∑ ε : Configuration d, ∏ l : Fin d, f l (ε l)) = ∏ l : Fin d, ∑ b : Bool, f l b := by
  simpa only [Fintype.piFinset_univ] using Finset.sum_prod_piFinset Finset.univ f

theorem sum_spin_exp (x : ℝ) : (∑ b : Bool, Real.exp (x * spin b)) = 2 * Real.cosh x := by
  simp [Fintype.sum_bool, spin, Real.cosh_eq]
  ring

theorem sum_spin_mul_exp (x : ℝ) :
    (∑ b : Bool, spin b * Real.exp (x * spin b)) = 2 * Real.sinh x := by
  simp [Fintype.sum_bool, spin, Real.sinh_eq]
  ring

def replicaTerminalBasePartition {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∑ ε : Configuration d, Real.exp (∑ l : Fin d, x l * spin (ε l))

theorem replicaTerminalBasePartition_eq {d : ℕ} (x : Fin d → ℝ) :
    replicaTerminalBasePartition x = ∏ l : Fin d, 2 * Real.cosh (x l) := by
  simp only [replicaTerminalBasePartition, Real.exp_sum]
  rw [sum_configuration_prod (fun l b => Real.exp (x l * spin b))]
  simp only [sum_spin_exp]

theorem replicaTerminalBasePartition_pos {d : ℕ} (x : Fin d → ℝ) :
    0 < replicaTerminalBasePartition x := by
  rw [replicaTerminalBasePartition_eq]
  exact Finset.prod_pos fun l _ => mul_pos (by norm_num) (Real.cosh_pos _)

theorem replicaTerminalProduct_sum {d : ℕ} (J : Finset (Fin d)) (x : Fin d → ℝ) :
    (∑ ε : Configuration d, replicaSpinProduct J ε *
      Real.exp (∑ l : Fin d, x l * spin (ε l))) =
      replicaTerminalBasePartition x * ∏ l ∈ J, Real.tanh (x l) := by
  classical
  have he (ε : Configuration d) : replicaSpinProduct J ε *
      Real.exp (∑ l : Fin d, x l * spin (ε l)) =
      ∏ l : Fin d, (if l ∈ J then spin (ε l) else 1) * Real.exp (x l * spin (ε l)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, ← Real.exp_sum]
    rfl
  simp_rw [he]
  rw [sum_configuration_prod (fun l b => (if l ∈ J then spin b else 1) * Real.exp (x l * spin b))]
  have hc (l : Fin d) :
      (∑ b : Bool, (if l ∈ J then spin b else 1) * Real.exp (x l * spin b)) =
      (2 * Real.cosh (x l)) * (if l ∈ J then Real.tanh (x l) else 1) := by
    by_cases hl : l ∈ J
    · simp only [hl, ite_true, sum_spin_mul_exp, Real.tanh_eq_sinh_div_cosh]
      field_simp [(Real.cosh_pos (x l)).ne']
    · simp only [hl, ite_false, one_mul, sum_spin_exp, mul_one]
  simp_rw [hc]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, replicaTerminalBasePartition_eq]

theorem exp_source_product {d : ℕ} (J : Finset (Fin d)) (ε : Configuration d) (θ : ℝ) :
    Real.exp (θ * replicaSpinProduct J ε) =
      Real.cosh θ + replicaSpinProduct J ε * Real.sinh θ := by
  have H := replicaSpinProduct_sq J ε
  by_cases hP : replicaSpinProduct J ε = 1
  · rw [hP, mul_one, one_mul, Real.cosh_add_sinh]
  · have hN : replicaSpinProduct J ε = -1 :=
      (eq_or_eq_neg_of_sq_eq_sq (replicaSpinProduct J ε) 1 (by simpa only [one_pow] using H)).resolve_left hP
    rw [hN, mul_neg_one, neg_one_mul]
    simpa only [sub_eq_add_neg] using (Real.cosh_sub_sinh θ).symm

theorem replicaTerminalPartition_source {d : ℕ} (J : Finset (Fin d)) (θ : ℝ) (x : Fin d → ℝ) :
    (∑ ε : Configuration d,
      Real.exp ((∑ l : Fin d, x l * spin (ε l)) + θ * replicaSpinProduct J ε)) =
      replicaTerminalBasePartition x *
        (Real.cosh θ + (∏ l ∈ J, Real.tanh (x l)) * Real.sinh θ) := by
  simp_rw [Real.exp_add, exp_source_product, mul_add]
  rw [Finset.sum_add_distrib]
  have he (ε : Configuration d) :
      Real.exp (∑ l : Fin d, x l * spin (ε l)) * (replicaSpinProduct J ε * Real.sinh θ) =
      (replicaSpinProduct J ε * Real.exp (∑ l : Fin d, x l * spin (ε l))) * Real.sinh θ := by ring
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.sum_mul, replicaTerminalProduct_sum]
  dsimp only [replicaTerminalBasePartition]
  ring

theorem replicaSourceTerminal_ratio {d : ℕ} (J : Finset (Fin d)) (θ : ℝ) (x : Fin d → ℝ) :
    Real.exp (replicaSourceTerminal J θ x - replicaSourceTerminal J 0 x) =
      Real.cosh θ + (∏ l ∈ J, Real.tanh (x l)) * Real.sinh θ := by
  have hp : 0 < ∑ ε : Configuration d,
      Real.exp ((∑ l : Fin d, x l * spin (ε l)) + θ * replicaSpinProduct J ε) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [replicaSourceTerminal, zero_mul, add_zero]
  change Real.exp (Real.log _ - Real.log (replicaTerminalBasePartition x)) = _
  rw [Real.exp_sub, Real.exp_log hp, Real.exp_log (replicaTerminalBasePartition_pos x)]
  rw [replicaTerminalPartition_source]
  exact mul_div_cancel_left₀ _ (replicaTerminalBasePartition_pos x).ne'

end OverlapPaper
