module
public import OverlapPaper.BlockCovariance
public import OverlapPaper.FiniteIntegrability

@[expose] public section

/-! Exact factorization of the independent mixed physical block partition function. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OverlapPaper
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem totalHamiltonian_block {n m : ℕ} (h : ℝ) (g : Disorder n × Disorder m)
    (σ : Configuration (n + m)) :
    totalHamiltonian h (blockHamiltonian g) σ =
      totalHamiltonian h g.1 (SpinGlass.cfgLeft (N := n) (M := m) σ) +
      totalHamiltonian h g.2 (SpinGlass.cfgRight (N := n) (M := m) σ) := by
  simp only [totalHamiltonian, hamiltonian, blockHamiltonian, WithLp.ofLp_toLp,
    Fin.sum_univ_add, SpinGlass.cfgLeft, SpinGlass.cfgRight]
  ring

theorem partitionFunction_block {n m : ℕ} (h : ℝ) (g : Disorder n × Disorder m) :
    partitionFunction h (blockHamiltonian g) = partitionFunction h g.1 * partitionFunction h g.2 := by
  classical
  unfold partitionFunction
  calc
    (∑ σ : Configuration (n + m), Real.exp (totalHamiltonian h (blockHamiltonian g) σ)) =
        ∑ p : Configuration n × Configuration m,
          Real.exp (totalHamiltonian h (blockHamiltonian g) ((SpinGlass.cfgEquiv n m).symm p)) := by
      exact Fintype.sum_equiv (SpinGlass.cfgEquiv n m) _ _ (fun σ => by simp)
    _ = ∑ p : Configuration n × Configuration m,
        Real.exp (totalHamiltonian h g.1 p.1) * Real.exp (totalHamiltonian h g.2 p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [totalHamiltonian_block]
      change Real.exp (totalHamiltonian h g.1
          (SpinGlass.cfgLeft n m (SpinGlass.cfgJoin n m p.1 p.2)) + totalHamiltonian h g.2
          (SpinGlass.cfgRight n m (SpinGlass.cfgJoin n m p.1 p.2))) = _
      rw [SpinGlass.cfgLeft_join, SpinGlass.cfgRight_join, Real.exp_add]
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

theorem log_partitionFunction_block {n m : ℕ} (h : ℝ) (g : Disorder n × Disorder m) :
    Real.log (partitionFunction h (blockHamiltonian g)) =
      Real.log (partitionFunction h g.1) + Real.log (partitionFunction h g.2) := by
  rw [partitionFunction_block,
    Real.log_mul (partitionFunction_pos h g.1).ne' (partitionFunction_pos h g.2).ne']

theorem integral_log_partitionFunction_block (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (n m : ℕ) (h : ℝ) :
    (∫ g : Disorder n × Disorder m, Real.log (partitionFunction h (blockHamiltonian g))
      ∂(disorderLaw ξ n).prod (disorderLaw ξ m)) =
      (∫ g : Disorder n, Real.log (partitionFunction h g) ∂disorderLaw ξ n) +
      ∫ g : Disorder m, Real.log (partitionFunction h g) ∂disorderLaw ξ m := by
  have hfst : HasLaw (Prod.fst : Disorder n × Disorder m → Disorder n) (disorderLaw ξ n)
      ((disorderLaw ξ n).prod (disorderLaw ξ m)) := measurePreserving_fst.hasLaw
  have hsnd : HasLaw (Prod.snd : Disorder n × Disorder m → Disorder m) (disorderLaw ξ m)
      ((disorderLaw ξ n).prod (disorderLaw ξ m)) := measurePreserving_snd.hasLaw
  have hn := hfst.integrable_comp (integrable_log_partitionFunction ξ (n := n) h)
  have hm := hsnd.integrable_comp (integrable_log_partitionFunction ξ (n := m) h)
  simp only [Function.comp_def] at hn hm
  simp_rw [log_partitionFunction_block]
  rw [integral_add hn hm]
  have hiN := hfst.integral_comp (integrable_log_partitionFunction ξ (n := n) h).aestronglyMeasurable
  have hiM := hsnd.integral_comp (integrable_log_partitionFunction ξ (n := m) h).aestronglyMeasurable
  exact congrArg₂ HAdd.hAdd hiN hiM

end OverlapPaper
