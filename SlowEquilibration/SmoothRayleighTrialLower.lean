-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SmoothRayleighTrialRepresentation

/-! The literal smooth min-max trials bound the actual spherical generator
eigenvalues. Positivity is proved from their actual Gibbs mass. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarCusp
open MeasureTheory Set Function Module
open SphericalModel SphericalForm
open scoped ContDiff InnerProductSpace
set_option maxHeartbeats 600000
variable {N : ℕ}

lemma literal_trial_nonneg {π : Measure (Vector N)} {k : ℕ} {b : ℝ}
    (ht : SlowEquilibrationCuspSource.RayleighTrial π k b) : 0≤b := by
  obtain ⟨U,hU,hdim,_hsmooth,hmass,hbound⟩ := ht
  let : FiniteDimensional ℝ U := hU
  obtain ⟨u,hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    ((Nat.zero_le k).trans_lt hdim)
  have hf : u.val≠0 := fun h => hu (Subtype.ext h)
  have hp := hmass u.val u.property hf
  have he := integral_nonneg (μ := π) (fun x => sq_nonneg
    ‖SlowEquilibrationCuspSource.sphericalGradient u.val x‖)
  have hb := hbound u.val u.property
  nlinarith

lemma literal_trial_eigenvalue_le (hN : 2≤N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (D : SphericalSpectralData hN β H hH.continuous) (k : ℕ) (b : ℝ)
    (ht : SlowEquilibrationCuspSource.RayleighTrial (gibbsLaw N β H) k b) :
    D.eigenvalue k≤b := by
  obtain ⟨U,hU,hdim,hsmooth,hpositive,hbound⟩ := ht
  let : FiniteDimensional ℝ U := hU
  let hN₁ : 1≤N := by omega
  let J := sphericalEnergyL2Map hN₁ β H hH.continuous
  let SM := smoothEnergyToGraph hN₁ β H hH.continuous
  let L : U →ₗ[ℝ] smoothCore N :=
    U.subtype.codRestrict _ (fun u => hsmooth u.val u.property)
  let T := SM.comp L
  have hmass (u : U) : ‖J (T u)‖^2=∫ x,(u.val x)^2 ∂gibbsLaw N β H := by
    change ‖J (SM (L u))‖^2=_
    rw [sphericalEnergyL2Map_smooth,←real_inner_self_eq_norm_sq,gibbsToL2_inner]
    apply integral_congr_ae
    exact .of_forall (fun x => by change u.val x*u.val x=u.val x^2; ring)
  have henergy (u : U) : FormMinMax.formEnergy J (T u)=
      ∫ x,‖SlowEquilibrationCuspSource.sphericalGradient u.val x‖^2 ∂gibbsLaw N β H := by
    change FormMinMax.formEnergy J (SM (L u))=_
    rw [formEnergy_eq_sphericalCompletedDirichlet,
      sphericalCompletedDirichlet_smooth_energy]
    simp only [dirichletEnergy,dirichletForm,source_surfaceGradient_eq,
      real_inner_self_eq_norm_sq]
    rfl
  have hT : Injective T := by
    rw [injective_iff_map_eq_zero]
    intro u hz
    by_contra hu
    have hp := hpositive u.val u.property (fun h => hu (Subtype.ext h))
    rw [←hmass u,hz,map_zero,norm_zero,zero_pow (by omega)] at hp
    exact (lt_irrefl 0) hp
  let V := LinearMap.range T
  let : FiniteDimensional ℝ V := LinearMap.finiteDimensional_range T
  have hdimV : k<finrank ℝ V := by
    rw [LinearMap.finrank_range_of_inj hT]
    exact hdim
  have hb : ∀ v∈V,FormMinMax.formEnergy J v≤b*‖J v‖^2 := by
    rintro v ⟨u,rfl⟩
    rw [henergy,hmass]
    exact hbound u.val u.property
  by_contra hn
  have hJ : Injective J := sphericalEnergyL2Map_injective hN₁ β H hH
  have he : ∀ j,J ((ContinuousLinearMap.adjoint (𝕜 := ℝ) J) (D.basis j))=
      D.resolventEigenvalue j • D.basis j := by
    intro j
    change sphericalL2Resolvent hN₁ β H hH.continuous (D.basis j)=_
    exact D.eigen j
  have hle : finrank ℝ V≤k := @FormMinMax.finrank_le_of_rayleigh_bound_lt
    (Lp ℝ 2 (gibbsLaw N β H))
    (sphericalSobolevGraph hN₁ β H hH.continuous)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance J
    hJ D.basis D.resolventEigenvalue (fun j => (D.bounds j).1) he D.generator_monotone
    k b (lt_of_not_ge hn) V inferInstance hb
  omega

end SlowEquilibration.PalomarCusp
