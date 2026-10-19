-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CuspSourceDefinitions
public import SlowEquilibration.SphericalSpectralComparison
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual ambient smooth Rayleigh trial spaces extracted from the completed
spherical Gibbs form. This is a representation bridge for a readable spectral
Challenge; no spectrum bound is built into its statement objects. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarCusp
open MeasureTheory Set Function Module
open SphericalModel SphericalForm
open scoped ContDiff InnerProductSpace
set_option maxHeartbeats 500000
variable {N : ℕ}

lemma source_surfaceGradient_eq (f : Vector N → ℝ) (x : Vector N) :
    SlowEquilibrationCuspSource.sphericalGradient f x=surfaceGradient f x := by
  simp only [SlowEquilibrationCuspSource.sphericalGradient,surfaceGradient,
    tangentProjection_apply,SphericalAging.HardSphereDynamics.projection,gradient]

lemma source_gibbsLaw_eq (β : ℝ) (H : Vector N → ℝ) :
    SlowEquilibrationCuspSource.gibbsLaw β H=gibbsLaw N β H := by
  rfl

/-- A genuine finite-dimensional trial in the smooth graph has actual globally
smooth ambient representatives, chosen linearly, and preserves its literal
Gibbs L² mass and intrinsic gradient energy. -/
theorem core_trial_representation (hN : 1≤N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (k : ℕ) (b : ℝ)
    (ht : FormMinMax.CoreRayleighTrialBound
      (H := Lp ℝ 2 (gibbsLaw N β H))
      (F := sphericalSobolevGraph hN β H hH.continuous)
      (sphericalEnergyL2Map hN β H hH.continuous)
      (smoothGraphCore hN β H hH.continuous) k b) :
    SlowEquilibrationCuspSource.RayleighTrial (gibbsLaw N β H) k b := by
  obtain ⟨U,hcore,hU,hdim,hbound⟩ := ht
  let : FiniteDimensional ℝ U := hU
  let J := sphericalEnergyL2Map hN β H hH.continuous
  let SM := smoothEnergyToGraph hN β H hH.continuous
  let Core := smoothGraphCore hN β H hH.continuous
  let : Module.Free ℝ SM.range := Module.Free.of_divisionRing ℝ SM.range
  let : Projective ℝ SM.range := Module.Projective.of_free
  obtain ⟨S,hS⟩ := SM.rangeRestrict.exists_rightInverse_of_surjective SM.range_rangeRestrict
  let L₀ : U →ₗ[ℝ] Core := U.subtype.codRestrict _ (fun u => hcore u.property)
  let T : U →ₗ[ℝ] (Vector N → ℝ) := (smoothCore N).subtype.comp (S.comp L₀)
  have hST (u : U) : SM (S (L₀ u))=u.val := by
    have hh := LinearMap.congr_fun hS (L₀ u)
    exact congrArg Subtype.val hh
  have hT : Injective T := by
    intro u v h
    have hh : S (L₀ u)=S (L₀ v) := Subtype.ext h
    have hg := congrArg SM hh
    rw [hST,hST] at hg
    exact Subtype.ext hg
  have hmass (u : U) : ‖J u.val‖^2=∫ x,(T u x)^2 ∂gibbsLaw N β H := by
    rw [←hST u,sphericalEnergyL2Map_smooth,
      ←real_inner_self_eq_norm_sq,gibbsToL2_inner]
    apply integral_congr_ae
    exact .of_forall (fun x => by
      change (S (L₀ u)).val x*(S (L₀ u)).val x=(S (L₀ u)).val x^2
      ring)
  have henergy (u : U) : FormMinMax.formEnergy J u.val=
      ∫ x,‖SlowEquilibrationCuspSource.sphericalGradient (T u) x‖^2 ∂gibbsLaw N β H := by
    rw [←hST u,formEnergy_eq_sphericalCompletedDirichlet,
      sphericalCompletedDirichlet_smooth_energy]
    simp only [dirichletEnergy,dirichletForm,source_surfaceGradient_eq,
      real_inner_self_eq_norm_sq]
    rfl
  refine ⟨LinearMap.range T,LinearMap.finiteDimensional_range T,?_,?_,?_,?_⟩
  · rw [LinearMap.finrank_range_of_inj hT]
    rw [hdim]
    exact Nat.lt_succ_self k
  · rintro f ⟨u,rfl⟩
    exact (S (L₀ u)).property
  · rintro f ⟨u,rfl⟩ hf
    have hu : u≠0 := by
      intro hz
      apply hf
      simp only [hz,map_zero]
    have hg : J u.val≠0 := by
      intro hz
      apply hu
      apply Subtype.ext
      exact sphericalEnergyL2Map_injective hN β H hH (hz.trans (map_zero J).symm)
    rw [←hmass]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg)
  · rintro f ⟨u,rfl⟩
    have hb := hbound u.val u.property
    rw [henergy,hmass] at hb
    exact hb

end SlowEquilibration.PalomarCusp
