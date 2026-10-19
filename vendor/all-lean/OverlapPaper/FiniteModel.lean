module
public import OverlapPaper.FiniteKernel
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! A genuine finite Gaussian realization with the exact mixed-model covariance.
The explicit countable interaction-series law bridge is proved separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators Topology
namespace OverlapPaper

abbrev Configuration (n : ℕ) := Fin n→Bool
def spin (b : Bool) : ℝ := if b then 1 else -1
@[simp] theorem abs_spin (b : Bool) : |spin b|=1 := by cases b <;> norm_num [spin]
@[simp] theorem spin_sq (b : Bool) : spin b^2=1 := by cases b <;> norm_num [spin]
@[simp] theorem spin_mul_self (b : Bool) : spin b*spin b=1 := by
  simpa only [pow_two] using spin_sq b

def overlap {n : ℕ} (σ τ : Configuration n) : ℝ :=
  (∑i:Fin n,spin (σ i)*spin (τ i))/(n:ℝ)

theorem overlap_symm {n : ℕ} (σ τ : Configuration n) : overlap σ τ=overlap τ σ := by
  simp only [overlap,mul_comm]

theorem abs_overlap_le_one {n : ℕ} (σ τ : Configuration n) : |overlap σ τ|≤1 := by
  have hs : |∑i:Fin n,spin (σ i)*spin (τ i)|≤(n:ℝ) := by
    calc
      _≤∑i:Fin n,|spin (σ i)*spin (τ i)| := Finset.abs_sum_le_sum_abs _ _
      _=(n:ℝ) := by simp [abs_mul]
  rw [overlap,abs_div,abs_of_nonneg (show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg _)]
  by_cases hn : n=0
  · simp [hn] at *
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hs

theorem overlap_mem_unit {n : ℕ} (σ τ : Configuration n) :
    overlap σ τ∈Icc (-1:ℝ) 1 := abs_le.mp (abs_overlap_le_one σ τ)

@[simp] theorem overlap_self {n : ℕ} (hn : 0<n) (σ : Configuration n) :
    overlap σ σ=1 := by
  simp only [overlap,spin_mul_self,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  exact div_self (by exact_mod_cast hn.ne')

def overlapMatrix (n : ℕ) : Matrix (Configuration n) (Configuration n) ℝ :=
  fun σ τ=>overlap σ τ

theorem overlapMatrix_posSemidef (n : ℕ) : (overlapMatrix n).PosSemidef := by
  have hh : (∑i:Fin n,Matrix.vecMulVec (fun σ:Configuration n=>spin (σ i))
      (star (fun σ:Configuration n=>spin (σ i)))).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i hi
    exact Matrix.posSemidef_vecMulVec_self_star _
  convert hh.smul (show (0:ℝ)≤1/(n:ℝ) by positivity) using 1
  ext σ τ
  simp only [overlapMatrix,overlap,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,
    Matrix.vecMulVec_apply,star_trivial]
  ring

def finiteCovariance (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) :
    Matrix (Configuration n) (Configuration n) ℝ :=
  fun σ τ=>(n:ℝ)*ξ.value (overlap σ τ)

theorem finiteCovariance_posSemidef (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) :
    (finiteCovariance ξ n).PosSemidef := by
  have he : finiteCovariance ξ n=(n:ℝ) • mixtureKernel ξ (overlapMatrix n) := by
    ext σ τ
    simp [finiteCovariance,mixtureKernel,overlapMatrix]
  rw [he]
  exact (mixture_kernel_posSemidef ξ (overlapMatrix_posSemidef n)
    (fun σ τ=>abs_overlap_le_one σ τ)).smul (show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg _)

abbrev Disorder (n : ℕ) := EuclideanSpace ℝ (Configuration n)
def disorderLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) : Measure (Disorder n) :=
  multivariateGaussian 0 (finiteCovariance ξ n)

instance disorderLaw_isProbabilityMeasure (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) :
    IsProbabilityMeasure (disorderLaw ξ n) := by unfold disorderLaw;infer_instance

instance disorderLaw_isGaussian (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) :
    IsGaussian (disorderLaw ξ n) := by unfold disorderLaw;infer_instance

def hamiltonian {n : ℕ} (g : Disorder n) (σ : Configuration n) : ℝ := g σ
def totalHamiltonian {n : ℕ} (h : ℝ) (g : Disorder n) (σ : Configuration n) : ℝ :=
  hamiltonian g σ+h*∑i:Fin n,spin (σ i)

theorem covariance_hamiltonian (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ)
    (σ τ : Configuration n) :
    cov[fun g:Disorder n=>hamiltonian g σ,fun g=>hamiltonian g τ;disorderLaw ξ n]
      =(n:ℝ)*ξ.value (overlap σ τ) :=
  covariance_eval_multivariateGaussian (finiteCovariance_posSemidef ξ n) σ τ

def partitionFunction {n : ℕ} (h : ℝ) (g : Disorder n) : ℝ :=
  ∑σ:Configuration n,Real.exp (totalHamiltonian h g σ)

theorem partitionFunction_pos {n : ℕ} (h : ℝ) (g : Disorder n) :
    0<partitionFunction h g :=
  Finset.sum_pos (fun _ _=>Real.exp_pos _) Finset.univ_nonempty

def gibbsWeight {n : ℕ} (h : ℝ) (g : Disorder n) (σ : Configuration n) : ℝ :=
  Real.exp (totalHamiltonian h g σ)/partitionFunction h g

theorem gibbsWeight_pos {n : ℕ} (h : ℝ) (g : Disorder n) (σ : Configuration n) :
    0<gibbsWeight h g σ := div_pos (Real.exp_pos _) (partitionFunction_pos h g)

theorem sum_gibbsWeight {n : ℕ} (h : ℝ) (g : Disorder n) :
    ∑σ:Configuration n,gibbsWeight h g σ=1 := by
  simp only [gibbsWeight,←Finset.sum_div]
  exact div_self (partitionFunction_pos h g).ne'

def gibbsPMF {n : ℕ} (h : ℝ) (g : Disorder n) : PMF (Configuration n) :=
  PMF.ofFintype (fun σ=>ENNReal.ofReal (gibbsWeight h g σ)) (by
    rw [←ENNReal.ofReal_sum_of_nonneg (fun σ _=>(gibbsWeight_pos h g σ).le),sum_gibbsWeight]
    norm_num)

def gibbsLaw {n : ℕ} (h : ℝ) (g : Disorder n) : Measure (Configuration n) :=
  (gibbsPMF h g).toMeasure

instance gibbsLaw_isProbabilityMeasure {n : ℕ} (h : ℝ) (g : Disorder n) :
    IsProbabilityMeasure (gibbsLaw h g) := by unfold gibbsLaw;infer_instance

def freeEnergy {n : ℕ} (h : ℝ) (g : Disorder n) : ℝ :=
  Real.log (partitionFunction h g)/(n:ℝ)
def expectedFreeEnergy (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) (n : ℕ) : ℝ :=
  ∫g,freeEnergy h g ∂disorderLaw ξ n

end OverlapPaper
