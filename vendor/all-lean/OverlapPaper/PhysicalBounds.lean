module
public import OverlapPaper.FiniteIntegrability
public import ParisiFormula.AnnealedBound

@[expose] public section

/-! The mixed physical model has a genuine, size-independent annealed bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OverlapPaper

theorem integral_exp_totalHamiltonian (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n : ℕ} (hn : 0 < n) (h : ℝ) (σ : Configuration n) :
    (∫ g : Disorder n, Real.exp (totalHamiltonian h g σ) ∂disorderLaw ξ n) =
      Real.exp (h * ∑ i : Fin n, spin (σ i) + (n : ℝ) * ξ.value 1 / 2) := by
  have hp := measurePreserving_eval_multivariateGaussian (μ := (0 : Disorder n))
    (finiteCovariance_posSemidef ξ n) (i := σ)
  have hh := mgf_gaussianReal hp.hasLaw 1
  have hnonneg : 0 ≤ finiteCovariance ξ n σ σ := (finiteCovariance_posSemidef ξ n).diag_nonneg
  simp only [mgf, one_mul, one_pow, mul_one,
    Real.coe_toNNReal _ hnonneg] at hh
  rw [finiteCovariance, overlap_self hn] at hh
  have hh' : (∫ g : Disorder n, Real.exp (g σ) ∂disorderLaw ξ n) =
      Real.exp ((n : ℝ) * ξ.value 1 / 2) := by simpa [disorderLaw] using hh
  simp only [totalHamiltonian, hamiltonian, Real.exp_add]
  rw [integral_mul_const, hh']
  ring

theorem abs_magnetization_le {n : ℕ} (σ : Configuration n) :
    |∑ i : Fin n, spin (σ i)| ≤ (n : ℝ) := by
  calc
    |∑ i : Fin n, spin (σ i)| ≤ ∑ i : Fin n, |spin (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n : ℝ) := by simp

theorem integral_partitionFunction_le (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n : ℕ} (hn : 0 < n) (h : ℝ) :
    (∫ g : Disorder n, partitionFunction h g ∂disorderLaw ξ n) ≤
      (2 : ℝ) ^ n * Real.exp ((n : ℝ) * (|h| + ξ.value 1 / 2)) := by
  rw [show (fun g : Disorder n => partitionFunction h g) =
    fun g => ∑ σ : Configuration n, Real.exp (totalHamiltonian h g σ) by rfl,
    integral_finsetSum _ (fun σ _ => integrable_exp_totalHamiltonian ξ h σ)]
  calc
    (∑ σ : Configuration n, ∫ g : Disorder n, Real.exp (totalHamiltonian h g σ) ∂disorderLaw ξ n) ≤
        ∑ _σ : Configuration n, Real.exp ((n : ℝ) * (|h| + ξ.value 1 / 2)) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [integral_exp_totalHamiltonian ξ hn]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (abs_magnetization_le σ) (abs_nonneg h)
      have hterm := le_abs_self (h * ∑ i : Fin n, spin (σ i))
      rw [abs_mul] at hterm
      nlinarith
    _ = _ := by simp

theorem expectedFreeEnergy_upper (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n : ℕ} (hn : 0 < n) (h : ℝ) :
    expectedFreeEnergy ξ h n ≤ Real.log 2 + |h| + ξ.value 1 / 2 := by
  have hj := SpinGlass.integral_log_le_log_integral (μ := disorderLaw ξ n)
    (W := fun g : Disorder n => partitionFunction h g)
    (partitionFunction_pos h) (integrable_partitionFunction ξ h)
    (integrable_log_partitionFunction ξ h)
  have hp : 0 < ∫ g : Disorder n, partitionFunction h g ∂disorderLaw ξ n := by
    apply integral_pos_iff_support_of_nonneg (fun g => (partitionFunction_pos h g).le)
      (integrable_partitionFunction ξ h) |>.mpr
    have he : Function.support (fun g : Disorder n => partitionFunction h g) = Set.univ := by
      ext g
      simp [(partitionFunction_pos h g).ne']
    simp [he]
  have hlog := Real.log_le_log hp (integral_partitionFunction_le ξ hn h)
  have hne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Real.log_mul hne (Real.exp_ne_zero _), Real.log_exp, Real.log_pow] at hlog
  unfold expectedFreeEnergy freeEnergy
  rw [integral_div]
  apply (div_le_iff₀ (show 0 < (n : ℝ) by exact_mod_cast hn)).mpr
  nlinarith

theorem expectedFreeEnergy_bddAbove (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) :
    BddAbove (Set.range (fun n : ℕ => expectedFreeEnergy ξ h (n + 1))) := by
  refine ⟨Real.log 2 + |h| + ξ.value 1 / 2, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact expectedFreeEnergy_upper ξ (Nat.succ_pos n) h

end OverlapPaper
