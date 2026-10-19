module

public import SphericalAging.SphereGeneratorAlgebra

public section

/-! The actual spherical forward density operator is adjoint to the constructed
backward generator, by the proved uniform-sphere and Gibbs-current identities. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereForwardAdjoint

open MeasureTheory FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra
open scoped BigOperators

theorem lieDerivative_const {N : ℕ} (A : Operator N) (c : ℝ) (x : Vector N) :
    lieDerivative A (fun _ : Vector N => c) x=0 := by simp [lieDerivative]

/-- Pairing the actual forward divergence against a test function gives the genuine Gibbs current. -/
theorem forward_density_current_pairing {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ f : Vector N → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) (hf : ContDiff ℝ 1 f) :
    (∫ x : Vector N,f x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=
      -(∫ x : Vector N,ρ x*rotationGamma κ A (relativeLog β J ρ) f x ∂sphereLaw N) := by
  classical
  have hlog := relativeLog_contDiff β J (hρ.of_le (by norm_num)) hpos
  have hi₀ i : Integrable (fun x : Vector N => f x*
      lieDerivative (A i) (rotationFlux β J (A i) ρ) x) (sphereLaw N) :=
    continuous_sphere_integrable hN (hf.continuous.mul
      (lieDerivative_continuous _ (rotationFlux_contDiff β J _ hρ)))
  have hi₁ i : Integrable (fun x : Vector N => ρ x*
      (lieDerivative (A i) (relativeLog β J ρ) x*lieDerivative (A i) f x)) (sphereLaw N) :=
    continuous_sphere_integrable hN (hρ.continuous.mul
      ((lieDerivative_continuous _ hlog).mul (lieDerivative_continuous _ hf)))
  have he i : (∫ x : Vector N,f x*lieDerivative (A i) (rotationFlux β J (A i) ρ) x ∂sphereLaw N)=
      -(∫ x : Vector N,ρ x*
        (lieDerivative (A i) (relativeLog β J ρ) x*lieDerivative (A i) f x) ∂sphereLaw N) := by
    rw [sphere_lie_integration_by_parts hN _ (hA i) hf (rotationFlux_contDiff β J _ hρ)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [relativeLog_lieDerivative β J _ (hρ.of_le (by norm_num)) hpos x]
      field_simp [(hpos x).ne']
  have hfun₀ : (fun x : Vector N => f x*forwardDensitySlope κ β J A ρ x)=
      (fun x => κ*∑ i,f x*lieDerivative (A i) (rotationFlux β J (A i) ρ) x) := by
    funext x
    unfold forwardDensitySlope
    rw [← Finset.mul_sum]
    ring
  have hfun₁ : (fun x : Vector N => ρ x*rotationGamma κ A (relativeLog β J ρ) f x)=
      (fun x => κ*∑ i,ρ x*
        (lieDerivative (A i) (relativeLog β J ρ) x*lieDerivative (A i) f x)) := by
    funext x
    unfold rotationGamma
    rw [← Finset.mul_sum]
    ring
  rw [hfun₀,hfun₁,integral_const_mul,integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => hi₀ i),
    integral_finsetSum Finset.univ (fun i _ => hi₁ i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  ring

/-- Exact actual adjoint relation, with no forward/backward adjoint premise. -/
theorem forward_density_adjoint {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ f : Vector N → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) (hf : ContDiff ℝ 2 f) :
    (∫ x : Vector N,f x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=
      (∫ x : Vector N,ρ x*rotationGenerator κ β J A f x ∂sphereLaw N) := by
  have hh := weighted_generator_current_ibp hN κ β J A hA (hρ.of_le (by norm_num)) hpos
    (f := fun _ : Vector N => 1) contDiff_const hf
  have hz : rotationGamma κ A (fun _ : Vector N => 1) f=(fun _ => 0) := by
    funext x
    simp [rotationGamma,lieDerivative_const]
  simp only [mul_one,hz,mul_zero,integral_zero,neg_zero,zero_sub] at hh
  rw [hh]
  exact forward_density_current_pairing hN κ β J A hA hρ hpos (hf.of_le (by norm_num))

end SphericalAging.SphereForwardAdjoint
