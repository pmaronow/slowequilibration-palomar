module

public import SphericalAging.SphereGeneratorIntegrationByParts

public section

/-! Genuine differential product rule for the actual spherical rotation generator. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereGeneratorAlgebra

open FiniteModel SphericalIntegrationByParts SphereEntropyDissipation SphereGeneratorIntegrationByParts
open scoped BigOperators

theorem lieDerivative_add {N : ℕ} (A : Operator N) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : Vector N) :
    lieDerivative A (fun y => f y+g y) x=lieDerivative A f x+lieDerivative A g x := by
  unfold lieDerivative
  rw [fderiv_fun_add (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x),add_apply]

/-- Actual second rotation derivative of a product. -/
theorem lieDerivative_twice_mul {N : ℕ} (A : Operator N) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vector N) :
    lieDerivative A (lieDerivative A (fun y => f y*g y)) x=
      f x*lieDerivative A (lieDerivative A g) x+
      g x*lieDerivative A (lieDerivative A f) x+
      2*(lieDerivative A f x*lieDerivative A g x) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg₁ : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hLf := lieDerivative_contDiff A hf
  have hLg := lieDerivative_contDiff A hg
  have hfun : lieDerivative A (fun y => f y*g y)=
      (fun y => f y*lieDerivative A g y+g y*lieDerivative A f y) :=
    funext (lieDerivative_mul A hf₁ hg₁)
  rw [hfun,lieDerivative_add A (hf₁.mul hLg) (hg₁.mul hLf),
    lieDerivative_mul A hf₁ hLg,lieDerivative_mul A hg₁ hLf]
  ring

/-- Exact generator product rule, including its factor two. -/
theorem rotationGenerator_mul {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vector N) :
    rotationGenerator κ β J A (fun y => f y*g y) x=
      f x*rotationGenerator κ β J A g x+g x*rotationGenerator κ β J A f x+
      2*rotationGamma κ A f g x := by
  classical
  have hterm i : lieDerivative (A i) (lieDerivative (A i) (fun y => f y*g y)) x+
      β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) (fun y => f y*g y) x=
      f x*(lieDerivative (A i) (lieDerivative (A i) g) x+
        β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) g x)+
      g x*(lieDerivative (A i) (lieDerivative (A i) f) x+
        β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) f x)+
      2*(lieDerivative (A i) f x*lieDerivative (A i) g x) := by
    rw [lieDerivative_twice_mul _ hf hg,
      lieDerivative_mul _ (hf.of_le (by norm_num)) (hg.of_le (by norm_num))]
    ring
  unfold rotationGenerator rotationGamma
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum]
  ring

end SphericalAging.SphereGeneratorAlgebra
