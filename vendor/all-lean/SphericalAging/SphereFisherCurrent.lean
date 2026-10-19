module

public import SphericalAging.SphereCanonicalEntropy

public section

/-! Actual Cauchy--Schwarz control of the nonequilibrium Gibbs current,
from its genuine tangent score and the true probability density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereFisherCurrent

open MeasureTheory Set
open scoped InnerProductSpace Topology
open FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation
open SphereRotationGeometry HardSphereDynamics

/-- Smooth positive density gives a genuine continuous tangent Gibbs score. -/
theorem tangentScore_continuous {N p : ℕ} (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) :
    Continuous (tangentScore β J ρ) := by
  have hrel : ContDiff ℝ 2 (relativeLog β J ρ) :=
    ((hρ.log (fun x => (hpos x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  have hg : Continuous (gradient (relativeLog β J ρ)) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (hrel.continuous_fderiv (by norm_num))
  unfold tangentScore projection
  have hi : Continuous (fun x : Vector N => ⟪x,gradient (relativeLog β J ρ) x⟫_ℝ) :=
    continuous_id.inner hg
  convert hg.sub ((hi.div_const (N : ℝ)).smul continuous_id) using 1
  funext x
  rfl

/-- The actual weighted probability variance proves the square-integral bound. -/
theorem density_integral_square_le {N : ℕ} (hN : 0<N) {ρ f : Vector N → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f) (hpos : ∀ x,0≤ρ x)
    (hmass : (∫ x : Vector N,ρ x ∂sphereLaw N)=1) :
    (∫ x : Vector N,ρ x*f x ∂sphereLaw N)^2 ≤ ∫ x : Vector N,ρ x*(f x)^2 ∂sphereLaw N := by
  let a := ∫ x : Vector N,ρ x*f x ∂sphereLaw N
  have hv : 0≤(∫ x : Vector N,ρ x*(f x-a)^2 ∂sphereLaw N) :=
    integral_nonneg fun x => mul_nonneg (hpos x) (sq_nonneg _)
  have hfun : (fun x : Vector N => ρ x*(f x-a)^2)=
      (fun x => (ρ x*(f x)^2-(2*a)*(ρ x*f x))+a^2*ρ x) := by funext x;ring
  have hsq := continuous_sphere_integrable hN (hρ.mul (hf.pow 2))
  have hfint := continuous_sphere_integrable hN (hρ.mul hf)
  have hrint := continuous_sphere_integrable hN hρ
  rw [hfun,integral_add (f := fun x => ρ x*(f x)^2-(2*a)*(ρ x*f x))
    (g := fun x => a^2*ρ x) (hsq.sub (hfint.const_mul (2*a))) (hrint.const_mul (a^2)),
    integral_sub (f := fun x => ρ x*(f x)^2) (g := fun x => (2*a)*(ρ x*f x))
      hsq (hfint.const_mul (2*a)),integral_const_mul,integral_const_mul,hmass] at hv
  dsimp only [a] at hv
  nlinarith

/-- The actual normalized current entering the finite nonequilibrium FDT identity. -/
@[expose] def currentDefect {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ)
    (m : Vector N → Vector N) : ℝ :=
  (∫ x : Vector N,ρ x*⟪m x,tangentScore β J ρ x⟫_ℝ ∂sphereLaw N)/(N : ℝ)

/-- Genuine finite-dimensional current bound I/N from the true conditional-mean norm bound. -/
theorem currentDefect_fisher_bound {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x)
    (hmass : (∫ x : Vector N,ρ x ∂sphereLaw N)=1)
    {m : Vector N → Vector N} (hm : Continuous m)
    (hmean : ∀ x,OnSphere x → ‖m x‖^2 ≤ (N : ℝ)) :
    (currentDefect β J ρ m)^2 ≤ fisherInformation β J ρ/(N : ℝ) := by
  have hs := tangentScore_continuous β J hρ hpos
  have hinner : Continuous (fun x => ⟪m x,tangentScore β J ρ x⟫_ℝ) := hm.inner hs
  have hsq := density_integral_square_le hN hρ.continuous hinner (fun x => (hpos x).le) hmass
  have hi₁ := continuous_sphere_integrable hN (hρ.continuous.mul (hinner.pow 2))
  have hi₂ := continuous_sphere_integrable hN (hρ.continuous.mul (hs.norm.pow 2))
  have hpoint : ∀ᵐ x ∂sphereLaw N,ρ x*⟪m x,tangentScore β J ρ x⟫_ℝ^2 ≤
      (N : ℝ)*(ρ x*‖tangentScore β J ρ x‖^2) := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
    have hsch := real_inner_mul_inner_self_le (m x) (tangentScore β J ρ x)
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hsch
    have hnorm := hmean x hxs
    calc
      _ ≤ ρ x*(‖m x‖^2*‖tangentScore β J ρ x‖^2) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hsch]) (hpos x).le
      _ ≤ ρ x*((N : ℝ)*‖tangentScore β J ρ x‖^2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)) (hpos x).le
      _ = _ := by ring
  have hh := integral_mono_ae hi₁ (hi₂.const_mul (N : ℝ)) hpoint
  rw [integral_const_mul] at hh
  change (∫ x : Vector N,ρ x*⟪m x,tangentScore β J ρ x⟫_ℝ^2 ∂sphereLaw N) ≤
    (N : ℝ)*fisherInformation β J ρ at hh
  have hn : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  unfold currentDefect
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos hn 2) hn).mpr
  nlinarith only [mul_le_mul_of_nonneg_right (hsq.trans hh) hn.le]

end SphericalAging.SphereFisherCurrent
