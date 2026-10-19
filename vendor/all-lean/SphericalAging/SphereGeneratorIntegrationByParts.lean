module

public import SphericalAging.SphereCanonicalEntropy

public section

/-! Actual Gibbs-current integration by parts for the genuine spherical
rotation generator. It is derived from uniform-sphere rotation invariance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereGeneratorIntegrationByParts

open MeasureTheory Set
open scoped BigOperators
open FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation

@[expose] def rotationGamma {N : ℕ} {ι : Type*} [Fintype ι] (κ : ℝ) (A : ι → Operator N)
    (f g : Vector N → ℝ) (x : Vector N) : ℝ :=
  κ*∑ i,lieDerivative (A i) f x*lieDerivative (A i) g x

@[expose] def rotationGenerator {N p : ℕ} {ι : Type*} [Fintype ι] (κ β : ℝ) (J : Disorder N p)
    (A : ι → Operator N) (g : Vector N → ℝ) (x : Vector N) : ℝ :=
  κ*∑ i,(lieDerivative (A i) (lieDerivative (A i) g) x+
    β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) g x)

/-- The actual single-rotation weighted integration by parts. -/
theorem single_rotation_current_ibp {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    (A : Operator N) (hA : star A=-A) {ρ f g : Vector N → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x,0<ρ x)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    (∫ x : Vector N,ρ x*f x*(lieDerivative A (lieDerivative A g) x+
      β*lieDerivative A (Hamiltonian N p J) x*lieDerivative A g x) ∂sphereLaw N)=
      -(∫ x : Vector N,ρ x*(lieDerivative A f x*lieDerivative A g x) ∂sphereLaw N)-
      (∫ x : Vector N,ρ x*f x*(lieDerivative A (relativeLog β J ρ) x*lieDerivative A g x)
        ∂sphereLaw N) := by
  have hgc := lieDerivative_contDiff A hg
  have hρf := hρ.mul hf
  have hH := ((Hamiltonian_contDiff J).of_le (by simp) : ContDiff ℝ 1 (Hamiltonian N p J))
  have hlog := relativeLog_contDiff β J hρ hpos
  have hbase := sphere_lie_integration_by_parts hN A hA hρf hgc
  change (∫ x : Vector N,(ρ x*f x)*lieDerivative A (lieDerivative A g) x ∂sphereLaw N)=
    -(∫ x : Vector N,lieDerivative A g x*lieDerivative A (fun y => ρ y*f y) x ∂sphereLaw N) at hbase
  have hβc : Continuous (fun _ : Vector N => β) := continuous_const
  have hdiag := continuous_sphere_integrable hN
    ((hρ.continuous.mul hf.continuous).mul (lieDerivative_continuous A hgc))
  have hdrift := continuous_sphere_integrable hN
    ((hρ.continuous.mul hf.continuous).mul
      ((hβc.mul (lieDerivative_continuous A hH)).mul hgc.continuous))
  have hprod := continuous_sphere_integrable hN
    (hρ.continuous.mul ((lieDerivative_continuous A hf).mul hgc.continuous))
  have hcur := continuous_sphere_integrable hN
    ((hρ.continuous.mul hf.continuous).mul ((lieDerivative_continuous A hlog).mul hgc.continuous))
  have hrad := continuous_sphere_integrable hN
    (hgc.continuous.mul (lieDerivative_continuous A hρf))
  have hfun₀ : (fun x : Vector N => ρ x*f x*(lieDerivative A (lieDerivative A g) x+
      β*lieDerivative A (Hamiltonian N p J) x*lieDerivative A g x))=
      (fun x => (ρ x*f x)*lieDerivative A (lieDerivative A g) x+
        (ρ x*f x)*(β*lieDerivative A (Hamiltonian N p J) x*lieDerivative A g x)) := by funext x;ring
  have hfun₁ : (fun x : Vector N => -lieDerivative A g x*lieDerivative A (fun y => ρ y*f y) x+
        (ρ x*f x)*(β*lieDerivative A (Hamiltonian N p J) x*lieDerivative A g x))=
      (fun x => -ρ x*(lieDerivative A f x*lieDerivative A g x)-
        ρ x*f x*(lieDerivative A (relativeLog β J ρ) x*lieDerivative A g x)) := by
    funext x
    rw [lieDerivative_mul A hρ hf,relativeLog_lieDerivative β J A hρ hpos x]
    unfold rotationFlux
    field_simp [(hpos x).ne']
    ring
  rw [hfun₀,integral_add
    (f := fun x : Vector N => (ρ x*f x)*lieDerivative A (lieDerivative A g) x)
    (g := fun x : Vector N => (ρ x*f x)*(β*lieDerivative A (Hamiltonian N p J) x*lieDerivative A g x))
    hdiag hdrift,hbase]
  have hh := congrArg (fun q : Vector N → ℝ => ∫ x,q x ∂sphereLaw N) hfun₁
  rw [integral_add (f := fun x : Vector N => -lieDerivative A g x*
      lieDerivative A (fun y => ρ y*f y) x) (g := fun x => (ρ x*f x)*
        (β*lieDerivative A (Hamiltonian N p J) x*lieDerivative A g x))
      (hrad.neg.congr (ae_of_all _ fun x => by simp only [Pi.neg_apply,Pi.mul_apply,neg_mul])) hdrift,
    integral_sub (f := fun x : Vector N => -ρ x*(lieDerivative A f x*lieDerivative A g x))
      (g := fun x => ρ x*f x*(lieDerivative A (relativeLog β J ρ) x*lieDerivative A g x))
      (hprod.neg.congr (ae_of_all _ fun x => by dsimp only [Pi.neg_apply,Pi.mul_apply]; ring)) hcur] at hh
  have hnegrad : (∫ x : Vector N,-lieDerivative A g x*
      lieDerivative A (fun y => ρ y*f y) x ∂sphereLaw N)=
      -(∫ x : Vector N,lieDerivative A g x*lieDerivative A (fun y => ρ y*f y) x ∂sphereLaw N) := by
    simp_rw [neg_mul]
    rw [integral_neg]
  have hnegprod : (∫ x : Vector N,-ρ x*(lieDerivative A f x*lieDerivative A g x) ∂sphereLaw N)=
      -(∫ x : Vector N,ρ x*(lieDerivative A f x*lieDerivative A g x) ∂sphereLaw N) := by
    simp_rw [neg_mul]
    rw [integral_neg]
  rwa [hnegrad,hnegprod] at hh

/-- Actual full Gibbs-current integration by parts, with the exact forward-generator coefficients. -/
theorem weighted_generator_current_ibp {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ f g : Vector N → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x,0<ρ x)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    (∫ x : Vector N,ρ x*f x*rotationGenerator κ β J A g x ∂sphereLaw N)=
      -(∫ x : Vector N,ρ x*rotationGamma κ A f g x ∂sphereLaw N)-
      (∫ x : Vector N,ρ x*f x*rotationGamma κ A (relativeLog β J ρ) g x ∂sphereLaw N) := by
  classical
  have hg₁ : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hlog := relativeLog_contDiff β J hρ hpos
  have hH := ((Hamiltonian_contDiff J).of_le (by simp) : ContDiff ℝ 1 (Hamiltonian N p J))
  have hi₀ i : Integrable (fun x : Vector N => ρ x*f x*
      (lieDerivative (A i) (lieDerivative (A i) g) x+
        β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) g x)) (sphereLaw N) :=
    continuous_sphere_integrable hN ((hρ.continuous.mul hf.continuous).mul
      ((lieDerivative_continuous _ (lieDerivative_contDiff _ hg)).add
        ((continuous_const.mul (lieDerivative_continuous _ hH)).mul (lieDerivative_continuous _ hg₁))))
  have hi₁ i : Integrable (fun x : Vector N => ρ x*(lieDerivative (A i) f x*lieDerivative (A i) g x))
      (sphereLaw N) := continuous_sphere_integrable hN
    (hρ.continuous.mul ((lieDerivative_continuous _ hf).mul (lieDerivative_continuous _ hg₁)))
  have hi₂ i : Integrable (fun x : Vector N => ρ x*f x*
      (lieDerivative (A i) (relativeLog β J ρ) x*lieDerivative (A i) g x)) (sphereLaw N) :=
    continuous_sphere_integrable hN ((hρ.continuous.mul hf.continuous).mul
      ((lieDerivative_continuous _ hlog).mul (lieDerivative_continuous _ hg₁)))
  have hfun₀ : (fun x : Vector N => ρ x*f x*rotationGenerator κ β J A g x)=
      (fun x => κ*∑ i,ρ x*f x*(lieDerivative (A i) (lieDerivative (A i) g) x+
        β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) g x)) := by
    funext x
    unfold rotationGenerator
    rw [← Finset.mul_sum]
    ring
  have hfun₁ : (fun x : Vector N => ρ x*rotationGamma κ A f g x)=
      (fun x => κ*∑ i,ρ x*(lieDerivative (A i) f x*lieDerivative (A i) g x)) := by
    funext x
    unfold rotationGamma
    rw [← Finset.mul_sum]
    ring
  have hfun₂ : (fun x : Vector N => ρ x*f x*rotationGamma κ A (relativeLog β J ρ) g x)=
      (fun x => κ*∑ i,ρ x*f x*
        (lieDerivative (A i) (relativeLog β J ρ) x*lieDerivative (A i) g x)) := by
    funext x
    unfold rotationGamma
    rw [← Finset.mul_sum]
    ring
  rw [hfun₀,hfun₁,hfun₂,integral_const_mul,integral_const_mul,integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => hi₀ i),
    integral_finsetSum Finset.univ (fun i _ => hi₁ i),
    integral_finsetSum Finset.univ (fun i _ => hi₂ i)]
  simp_rw [single_rotation_current_ibp hN β J _ (hA _) hρ hpos hf hg]
  rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  ring

end SphericalAging.SphereGeneratorIntegrationByParts
