module

public import SphericalAging.SphereQuenchedFDT

public section

/-! The logarithmic Gibbs-density evolution is derived from the actual forward
probability flux. No logarithmic PDE or entropy/Fisher conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereLogDensityEquation

open FiniteModel SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereQuenchedFDT
open scoped BigOperators

theorem relativeLog_contDiff_two {N p : ℕ} (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) :
    ContDiff ℝ 2 (relativeLog β J ρ) :=
  ((hρ.log (fun x => (hpos x).ne')).sub
    (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const

/-- Exact current flux equals density times the actual Gibbs score. -/
theorem rotationFlux_eq_density_score {N p : ℕ} (β : ℝ) (J : Disorder N p)
    (A : Operator N) {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x,0<ρ x) :
    rotationFlux β J A ρ=(fun x => ρ x*lieDerivative A (relativeLog β J ρ) x) := by
  funext x
  have hh := (eq_div_iff (hpos x).ne').mp (relativeLog_lieDerivative β J A hρ hpos x)
  rw [← hh]
  ring

/-- The genuine forward PDE gives the actual log-density generator balance pointwise. -/
theorem forward_density_log_balance {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) (x : Vector N) :
    forwardDensitySlope κ β J A ρ x=ρ x*
      (rotationGenerator κ β J A (relativeLog β J ρ) x+
        rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) x) := by
  classical
  have hρ₁ : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hψ := relativeLog_contDiff_two β J hρ hpos
  have hrscore i : lieDerivative (A i) ρ x=ρ x*
      (lieDerivative (A i) (relativeLog β J ρ) x+β*lieDerivative (A i) (Hamiltonian N p J) x) := by
    have hh := relativeLog_lieDerivative β J (A i) hρ₁ hpos x
    unfold rotationFlux at hh
    field_simp [(hpos x).ne'] at hh
    linarith only [hh]
  have ht i : lieDerivative (A i) (rotationFlux β J (A i) ρ) x=
      ρ x*((lieDerivative (A i) (lieDerivative (A i) (relativeLog β J ρ)) x+
        β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) (relativeLog β J ρ) x)+
        lieDerivative (A i) (relativeLog β J ρ) x*lieDerivative (A i) (relativeLog β J ρ) x) := by
    rw [rotationFlux_eq_density_score β J (A i) hρ₁ hpos,
      lieDerivative_mul (A i) hρ₁ (lieDerivative_contDiff (A i) hψ),hrscore i]
    ring
  unfold forwardDensitySlope rotationGenerator rotationGamma
  simp_rw [ht]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  ring

/-- Actual time differentiation of the constructed logarithmic Gibbs density. -/
theorem relativeLog_time_hasDerivAt {N p : ℕ} (β : ℝ) (J : Disorder N p)
    {ρ : ℝ → Vector N → ℝ} {t d : ℝ} {x : Vector N}
    (hd : HasDerivAt (fun s => ρ s x) d t) (hpos : 0<ρ t x) :
    HasDerivAt (fun s => relativeLog β J (ρ s) x) (d/ρ t x) t := by
  exact ((hd.log hpos.ne').sub_const (β*Hamiltonian N p J x)).add_const
    (Real.log (SphereGibbsEntropy.partitionFunction N p β J))

/-- The actual density forward PDE proves ψdot=Lψ+Γ(ψ), with the correct Gibbs potential. -/
theorem logarithmic_density_pde_hasDerivAt {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {ρ : ℝ → Vector N → ℝ} {t : ℝ} {d : Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (ρ t)) (hpos : ∀ x,0<ρ t x)
    (hd : ∀ x,HasDerivAt (fun s => ρ s x) (d x) t)
    (hPDE : ∀ x,d x=forwardDensitySlope κ β J A (ρ t) x) (x : Vector N) :
    HasDerivAt (fun s => relativeLog β J (ρ s) x)
      (rotationGenerator κ β J A (relativeLog β J (ρ t)) x+
        rotationGamma κ A (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x) t := by
  have hh := relativeLog_time_hasDerivAt β J (hd x) (hpos x)
  rw [hPDE x,forward_density_log_balance κ β J A hρ hpos x] at hh
  simpa only [mul_div_cancel_left₀ _ (hpos x).ne'] using hh

end SphericalAging.SphereLogDensityEquation
