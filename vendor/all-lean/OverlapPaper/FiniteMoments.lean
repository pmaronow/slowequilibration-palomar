module
public import OverlapPaper.FiniteIntegrability

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
namespace OverlapPaper

theorem hamiltonian_memLp_two (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (σ : Configuration n) : MemLp (fun g : Disorder n => hamiltonian g σ) 2 (disorderLaw ξ n) := by
  have hG : HasGaussianLaw (id : Disorder n → Disorder n) (disorderLaw ξ n) :=
    IsGaussian.hasGaussianLaw_id
  exact (hG.map_fun (PiLp.proj 2 (fun _ : Configuration n => ℝ) σ)).memLp_two

theorem integral_hamiltonian_product (ξ : FourPapersCommon.AdmissibleEvenMixture) {n : ℕ}
    (σ τ : Configuration n) :
    (∫ g : Disorder n, hamiltonian g σ * hamiltonian g τ ∂disorderLaw ξ n) =
      (n : ℝ) * ξ.value (overlap σ τ) := by
  have hh := covariance_hamiltonian ξ n σ τ
  rw [covariance_eq_sub (hamiltonian_memLp_two ξ σ) (hamiltonian_memLp_two ξ τ),
    integral_hamiltonian ξ σ, integral_hamiltonian ξ τ] at hh
  simpa only [zero_mul, sub_zero, Pi.mul_apply] using hh

theorem integral_disorder_eq_zero (ξ : FourPapersCommon.AdmissibleEvenMixture) (n : ℕ) :
    (∫ g : Disorder n, g ∂disorderLaw ξ n) = 0 := by
  exact integral_id_multivariateGaussian

end OverlapPaper
