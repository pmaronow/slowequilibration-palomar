module

public import SphericalAging.SphereForwardAdjoint

public section

/-! The exact nonequilibrium FDT bracket, derived from actual generator product
calculus and genuine Gibbs-current integration by parts. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereFDTAlgebra

open MeasureTheory FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereForwardAdjoint
open scoped BigOperators

theorem rotationGamma_comm {N : ℕ} {ι : Type*} [Fintype ι] (κ : ℝ) (A : ι → Operator N)
    (f g : Vector N → ℝ) (x : Vector N) : rotationGamma κ A f g x=rotationGamma κ A g f x := by
  unfold rotationGamma
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rotationGamma_continuous {N : ℕ} {ι : Type*} [Fintype ι] (κ : ℝ) (A : ι → Operator N)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Continuous (rotationGamma κ A f g) := by
  classical
  unfold rotationGamma
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (lieDerivative_continuous _ hf).mul (lieDerivative_continuous _ hg))

theorem rotationGenerator_continuous {N p : ℕ} {ι : Type*} [Fintype ι] (κ β : ℝ)
    (J : Disorder N p) (A : ι → Operator N) {g : Vector N → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (rotationGenerator κ β J A g) := by
  classical
  unfold rotationGenerator
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (lieDerivative_continuous _ (lieDerivative_contDiff _ hg)).add
      ((continuous_const.mul (lieDerivative_continuous _ ((Hamiltonian_contDiff J).of_le (by simp)))).mul
        (lieDerivative_continuous _ (hg.of_le (by norm_num)))))

/-- The exact finite FDT bracket with its source sign and coefficient. -/
theorem generator_fdt_bracket {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ φ m : Vector N → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x,0<ρ x)
    (hφ : ContDiff ℝ 2 φ) (hm : ContDiff ℝ 2 m) :
    (∫ x : Vector N,ρ x*(rotationGenerator κ β J A (fun y => φ y*m y) x-
      φ x*rotationGenerator κ β J A m x) ∂sphereLaw N)=
      (∫ x : Vector N,ρ x*rotationGamma κ A φ m x ∂sphereLaw N)-
      (∫ x : Vector N,ρ x*m x*rotationGamma κ A (relativeLog β J ρ) φ x ∂sphereLaw N) := by
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hm₁ : ContDiff ℝ 1 m := hm.of_le (by norm_num)
  have hg := rotationGamma_continuous κ A hφ₁ hm₁
  have hLφ := rotationGenerator_continuous κ β J A hφ
  have hibp := weighted_generator_current_ibp hN κ β J A hA hρ hpos hm₁ hφ
  have hfun : (fun x : Vector N => ρ x*(rotationGenerator κ β J A (fun y => φ y*m y) x-
      φ x*rotationGenerator κ β J A m x))=
      (fun x => ρ x*m x*rotationGenerator κ β J A φ x+2*(ρ x*rotationGamma κ A φ m x)) := by
    funext x
    rw [rotationGenerator_mul κ β J A hφ hm]
    ring
  rw [hfun,integral_add
    (f := fun x : Vector N => ρ x*m x*rotationGenerator κ β J A φ x)
    (g := fun x : Vector N => 2*(ρ x*rotationGamma κ A φ m x))
      (continuous_sphere_integrable hN ((hρ.continuous.mul hm.continuous).mul hLφ))
      ((continuous_sphere_integrable hN (hρ.continuous.mul hg)).const_mul 2),
    integral_const_mul,hibp]
  simp_rw [rotationGamma_comm κ A m φ]
  ring

end SphericalAging.SphereFDTAlgebra
