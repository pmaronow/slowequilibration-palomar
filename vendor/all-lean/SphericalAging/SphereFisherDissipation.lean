module

public import SphericalAging.SphereLogDensityEquation

public section

/-! Actual rotation Γ₂ and its Fisher production algebra, derived from genuine
Gibbs-current integration by parts. The pointwise Bochner curvature bound and the
time/spatial derivative interchange are separate analytic prerequisites. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherDissipation

open MeasureTheory FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereForwardAdjoint SphereFDTAlgebra
open SphereLogDensityEquation
open scoped BigOperators

/-- The actual iterated carré du champ of the constructed spherical generator. -/
@[expose] def rotationGamma2 {N p : ℕ} {ι : Type*} [Fintype ι] (κ β : ℝ) (J : Disorder N p)
    (A : ι → Operator N) (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  (1/2)*(rotationGenerator κ β J A (rotationGamma κ A f f) x-
    2*rotationGamma κ A f (rotationGenerator κ β J A f) x)

theorem lieDerivative_contDiff_order {N : ℕ} (A : Operator N) {n : ℕ} {f : Vector N → ℝ}
    (hf : ContDiff ℝ (n+1) f) : ContDiff ℝ n (lieDerivative A f) := by
  unfold lieDerivative
  exact (hf.fderiv_right (by simp)).clm_apply A.contDiff

theorem rotationGamma_contDiff_order {N : ℕ} {ι : Type*} [Fintype ι]
    (κ : ℝ) (A : ι → Operator N) {n : ℕ} {f g : Vector N → ℝ}
    (hf : ContDiff ℝ (n+1) f) (hg : ContDiff ℝ (n+1) g) :
    ContDiff ℝ n (rotationGamma κ A f g) := by
  classical
  unfold rotationGamma
  exact contDiff_const.mul (ContDiff.sum (s := Finset.univ) fun i _ =>
    (lieDerivative_contDiff_order _ hf).mul (lieDerivative_contDiff_order _ hg))

theorem rotationGenerator_contDiff_one {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 3 f) : ContDiff ℝ 1 (rotationGenerator κ β J A f) := by
  classical
  unfold rotationGenerator
  exact contDiff_const.mul (ContDiff.sum (s := Finset.univ) fun i _ =>
    (lieDerivative_contDiff_order _ (lieDerivative_contDiff_order _ hf)).add
      ((contDiff_const.mul (lieDerivative_contDiff _ ((Hamiltonian_contDiff J).of_le (by simp)))).mul
        (lieDerivative_contDiff _ (hf.of_le (by norm_num)))))

theorem rotationGamma_add_right {N : ℕ} {ι : Type*} [Fintype ι] (κ : ℝ) (A : ι → Operator N)
    (f : Vector N → ℝ) {g h : Vector N → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (x : Vector N) : rotationGamma κ A f (fun y => g y+h y) x=
      rotationGamma κ A f g x+rotationGamma κ A f h x := by
  classical
  unfold rotationGamma
  simp_rw [lieDerivative_add _ hg hh,mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Genuine Gibbs-current algebra gives the exact minus-two Γ₂ Fisher production.
No Γ₂/Fisher production premise is supplied. -/
theorem fisher_production_gamma2 {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ : Vector N → ℝ}
    (hρ : ContDiff ℝ 3 ρ) (hpos : ∀ x,0<ρ x) :
    (∫ x : Vector N,ρ x*rotationGenerator κ β J A
        (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x ∂sphereLaw N)+
      2*(∫ x : Vector N,ρ x*rotationGamma κ A (relativeLog β J ρ)
        (fun y => rotationGenerator κ β J A (relativeLog β J ρ) y+
          rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) y) x ∂sphereLaw N)=
      -2*(∫ x : Vector N,ρ x*rotationGamma2 κ β J A (relativeLog β J ρ) x ∂sphereLaw N) := by
  have hψ : ContDiff ℝ 3 (relativeLog β J ρ) :=
    ((hρ.log (fun x => (hpos x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  have hρ₁ : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hψ₁ : ContDiff ℝ 1 (relativeLog β J ρ) := hψ.of_le (by norm_num)
  have hG : ContDiff ℝ 2 (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) :=
    rotationGamma_contDiff_order κ A hψ hψ
  have hL := rotationGenerator_contDiff_one κ β J A hψ
  have hG₁ := hG.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hiA := continuous_sphere_integrable hN (hρ.continuous.mul
    (rotationGenerator_continuous κ β J A hG))
  have hiB := continuous_sphere_integrable hN (hρ.continuous.mul
    (rotationGamma_continuous κ A hψ₁ hL))
  have hiC := continuous_sphere_integrable hN (hρ.continuous.mul
    (rotationGamma_continuous κ A hψ₁ hG₁))
  have hcurrent := weighted_generator_current_ibp hN κ β J A hA hρ₁ hpos
    (f := fun _ : Vector N => 1) contDiff_const hG
  have hz : rotationGamma κ A (fun _ : Vector N => 1)
      (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ))=(fun _ => 0) := by
    funext x
    simp [rotationGamma,lieDerivative_const]
  simp only [mul_one,hz,mul_zero,integral_zero,neg_zero,zero_sub] at hcurrent
  have hfunB : (fun x : Vector N => ρ x*rotationGamma κ A (relativeLog β J ρ)
      (fun y => rotationGenerator κ β J A (relativeLog β J ρ) y+
        rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) y) x)=
      (fun x => ρ x*rotationGamma κ A (relativeLog β J ρ)
        (rotationGenerator κ β J A (relativeLog β J ρ)) x+
        ρ x*rotationGamma κ A (relativeLog β J ρ)
          (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x) := by
    funext x
    rw [rotationGamma_add_right κ A _ hL hG₁]
    ring
  have hfunD : (fun x : Vector N => ρ x*rotationGamma2 κ β J A (relativeLog β J ρ) x)=
      (fun x => (1/2)*(ρ x*rotationGenerator κ β J A
        (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x-
        2*(ρ x*rotationGamma κ A (relativeLog β J ρ)
          (rotationGenerator κ β J A (relativeLog β J ρ)) x))) := by
    funext x
    unfold rotationGamma2
    ring
  rw [hfunB,integral_add
    (f := fun x : Vector N => ρ x*rotationGamma κ A (relativeLog β J ρ)
      (rotationGenerator κ β J A (relativeLog β J ρ)) x)
    (g := fun x : Vector N => ρ x*rotationGamma κ A (relativeLog β J ρ)
      (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x) hiB hiC,
    hfunD,integral_const_mul,integral_sub
    (f := fun x : Vector N => ρ x*rotationGenerator κ β J A
      (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x)
    (g := fun x : Vector N => 2*(ρ x*rotationGamma κ A (relativeLog β J ρ)
      (rotationGenerator κ β J A (relativeLog β J ρ)) x)) hiA (hiB.const_mul 2),
    integral_const_mul]
  linarith only [hcurrent]

end SphericalAging.SphereFisherDissipation
