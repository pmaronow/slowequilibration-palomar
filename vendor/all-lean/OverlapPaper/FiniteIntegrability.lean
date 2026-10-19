module
public import OverlapPaper.FiniteModel

@[expose] public section

/-! Every finite physical expectation uses genuinely integrable functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OverlapPaper

theorem integrable_hamiltonian (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (σ : Configuration n) : Integrable (fun g:Disorder n=>hamiltonian g σ) (disorderLaw ξ n) := by
  exact (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Configuration n=>ℝ) σ).integrable_comp
    (show Integrable id (disorderLaw ξ n) from IsGaussian.integrable_id)

theorem integral_hamiltonian (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (σ : Configuration n) : ∫g:Disorder n,hamiltonian g σ ∂disorderLaw ξ n=0 := by
  have hh := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Configuration n=>ℝ) σ).integral_comp_id_comm
    (show Integrable id (disorderLaw ξ n) from IsGaussian.integrable_id)
  simpa [hamiltonian,disorderLaw] using hh

theorem integrable_totalHamiltonian (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (h : ℝ) (σ : Configuration n) :
    Integrable (fun g:Disorder n=>totalHamiltonian h g σ) (disorderLaw ξ n) :=
  (integrable_hamiltonian ξ σ).add (integrable_const _)

theorem integrable_exp_totalHamiltonian (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (h : ℝ) (σ : Configuration n) :
    Integrable (fun g:Disorder n=>Real.exp (totalHamiltonian h g σ)) (disorderLaw ξ n) := by
  have hp := measurePreserving_eval_multivariateGaussian (μ:=(0:Disorder n))
    (finiteCovariance_posSemidef ξ n) (i:=σ)
  have hh := hp.integrable_comp_of_integrable (integrable_exp_mul_gaussianReal (μ:=0)
    (v:=(finiteCovariance ξ n σ σ).toNNReal) 1)
  simpa [Function.comp_def,totalHamiltonian,hamiltonian,disorderLaw,Real.exp_add] using
    hh.mul_const (Real.exp (h*∑i:Fin n,spin (σ i)))

theorem integrable_partitionFunction (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (h : ℝ) : Integrable (fun g:Disorder n=>partitionFunction h g) (disorderLaw ξ n) :=
  integrable_finsetSum _ (fun σ _=>integrable_exp_totalHamiltonian ξ h σ)

theorem continuous_totalHamiltonian {n : ℕ} (h : ℝ) (σ : Configuration n) :
    Continuous (fun g:Disorder n=>totalHamiltonian h g σ) := by
  unfold totalHamiltonian hamiltonian
  fun_prop

theorem continuous_partitionFunction {n : ℕ} (h : ℝ) :
    Continuous (fun g:Disorder n=>partitionFunction h g) := by
  unfold partitionFunction
  exact continuous_finsetSum _ (fun σ _=>Real.continuous_exp.comp (continuous_totalHamiltonian h σ))

theorem totalHamiltonian_le_log_partition {n : ℕ} (h : ℝ) (g : Disorder n)
    (σ : Configuration n) : totalHamiltonian h g σ≤Real.log (partitionFunction h g) := by
  have hh : Real.exp (totalHamiltonian h g σ)≤partitionFunction h g :=
    Finset.single_le_sum (fun _ _=>(Real.exp_pos _).le) (Finset.mem_univ σ)
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hh

theorem abs_log_partition_le {n : ℕ} (h : ℝ) (g : Disorder n) (σ : Configuration n) :
    |Real.log (partitionFunction h g)|≤partitionFunction h g+|totalHamiltonian h g σ| := by
  have hu := Real.log_le_sub_one_of_pos (partitionFunction_pos h g)
  have hl := totalHamiltonian_le_log_partition h g σ
  have hZ := partitionFunction_pos h g
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (totalHamiltonian h g σ)]
  · linarith [abs_nonneg (totalHamiltonian h g σ)]

theorem integrable_log_partitionFunction (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (h : ℝ) : Integrable (fun g:Disorder n=>Real.log (partitionFunction h g)) (disorderLaw ξ n) := by
  let σ : Configuration n:=fun _=>true
  apply ((integrable_partitionFunction ξ h).add (integrable_totalHamiltonian ξ h σ).abs).mono'
  · exact ((continuous_partitionFunction h).log
      (fun g=>(partitionFunction_pos h g).ne')).aestronglyMeasurable
  · filter_upwards [] with g
    simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_log_partition_le h g σ

theorem integrable_freeEnergy (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ} (h : ℝ) :
    Integrable (fun g:Disorder n=>freeEnergy h g) (disorderLaw ξ n) :=
  (integrable_log_partitionFunction ξ h).div_const _

end OverlapPaper
