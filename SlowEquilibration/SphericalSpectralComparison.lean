-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothCoreTransfer
public import SlowEquilibration.SphericalNormalizedBasis

@[expose] public section

/-! # Actual spherical eigenvalue comparison

Finite-dimensional smooth trial spaces are transferred linearly between
the genuine Gibbs form cores. Density supplies arbitrarily near-optimal
trials, so no smooth eigenfunction attainment is assumed.
-/

namespace SlowEquilibration.SphericalSpectralComparison
noncomputable section
open MeasureTheory Set Module Filter Function
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
variable {N : ℕ}

lemma core_trial_transfer (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) (k : ℕ) (c : ℝ)
    (hc : FormMinMax.CoreRayleighTrialBound
      (H := Lp ℝ 2 (gibbsLaw N β₀ H₀))
      (F := sphericalSobolevGraph hN β₀ H₀ hH₀.continuous)
      (sphericalEnergyL2Map hN β₀ H₀ hH₀.continuous)
      (smoothGraphCore hN β₀ H₀ hH₀.continuous) k c) :
    FormMinMax.RayleighTrialBound
      (H := Lp ℝ 2 (gibbsLaw N β₁ H₁))
      (F := sphericalSobolevGraph hN β₁ H₁ hH₁.continuous)
      (sphericalEnergyL2Map hN β₁ H₁ hH₁.continuous)
      k (Real.exp (u-l)*c) := by
  obtain ⟨U, hcore, hU, hdim, hb⟩ := hc
  letI : FiniteDimensional ℝ U := hU
  let L₀ : U →ₗ[ℝ] smoothGraphCore hN β₀ H₀ hH₀.continuous :=
    U.subtype.codRestrict _ (fun v => hcore v.property)
  let L := (smoothCoreTransfer hN β₀ β₁ hH₀ hH₁).comp L₀
  have hL₀ : Injective L₀ := by
    intro v w he
    have hvw := congrArg
      (fun z : smoothGraphCore hN β₀ H₀ hH₀.continuous => z.val) he
    exact Subtype.ext hvw
  have hL : Injective L := (smoothCoreTransfer_injective hN β₀ β₁ hH₀ hH₁).comp hL₀
  refine ⟨LinearMap.range L, LinearMap.finiteDimensional_range L, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hL]
    exact hdim
  · rintro v ⟨w, rfl⟩
    by_cases hw : w = 0
    · simp only [hw, map_zero, FormMinMax.formEnergy, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0), sub_self, mul_zero, le_refl]
    have hwcore : L₀ w ≠ 0 := by
      intro hz
      apply hw
      exact hL₀ (hz.trans (map_zero L₀).symm)
    have hwgraph : (w : sphericalSobolevGraph hN β₀ H₀ hH₀.continuous) ≠ 0 := by
      intro hz
      exact hw (Subtype.ext hz)
    have hJ₀ : 0 < ‖sphericalEnergyL2Map hN β₀ H₀ hH₀.continuous w.val‖^2 := by
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro hz
      apply hwgraph
      exact sphericalEnergyL2Map_injective hN β₀ H₀ hH₀ (hz.trans (map_zero _).symm)
    have hJ₁ : 0 < ‖sphericalEnergyL2Map hN β₁ H₁ hH₁.continuous (L w)‖^2 := by
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro hz
      have hzL := sphericalEnergyL2Map_injective hN β₁ H₁ hH₁ (hz.trans (map_zero _).symm)
      exact hw (hL (hzL.trans (map_zero L).symm))
    have hq₀ : FormMinMax.rayleighQuotient
        (sphericalEnergyL2Map hN β₀ H₀ hH₀.continuous) w.val ≤ c :=
      (div_le_iff₀ hJ₀).mpr (hb w.val w.property)
    have hq := smoothCoreTransfer_rayleigh_comparison hN β₀ β₁ hH₀ hH₁ hl hu
      (L₀ w) hwcore
    have hq₁ : FormMinMax.rayleighQuotient
        (sphericalEnergyL2Map hN β₁ H₁ hH₁.continuous) (L w) ≤ Real.exp (u-l)*c :=
      hq.trans (mul_le_mul_of_nonneg_left hq₀ (Real.exp_pos _).le)
    exact (div_le_iff₀ hJ₁).mp hq₁

lemma eigenvalue_le_of_trial (hN : 2 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (D : SphericalSpectralData hN β H hH.continuous) (k : ℕ) (c : ℝ)
    (hc : FormMinMax.RayleighTrialBound
      (H := Lp ℝ 2 (gibbsLaw N β H))
      (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous)
      (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous) k c) :
    D.eigenvalue k ≤ c := by
  by_contra hn
  obtain ⟨U, hU, hdim, hb⟩ := hc
  letI : FiniteDimensional ℝ U := hU
  let J : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous →L[ℝ] Lp ℝ 2 (gibbsLaw N β H) := sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous
  have hJ : Function.Injective J := sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hH
  have he : ∀ j, J ((ContinuousLinearMap.adjoint (𝕜 := ℝ) J) (D.basis j)) =
      D.resolventEigenvalue j • D.basis j := by
    intro j
    change sphericalL2Resolvent (show 1 ≤ N by omega) β H hH.continuous (D.basis j) = _
    exact D.eigen j
  have hmono : Monotone (FormMinMax.weight D.resolventEigenvalue) := D.generator_monotone
  have hlt : c < FormMinMax.weight D.resolventEigenvalue k := lt_of_not_ge hn
  have hle : finrank ℝ U ≤ k := @FormMinMax.finrank_le_of_rayleigh_bound_lt
    (Lp ℝ 2 (gibbsLaw N β H))
    (sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance J
    hJ D.basis
    D.resolventEigenvalue (fun j => (D.bounds j).1) he hmono
    k c hlt U hU hb
  omega

lemma exists_smooth_trial_above_eigenvalue (hN : 2 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (D : SphericalSpectralData hN β H hH.continuous) (k : ℕ) (c : ℝ)
    (hc : D.eigenvalue k < c) :
    FormMinMax.CoreRayleighTrialBound
      (H := Lp ℝ 2 (gibbsLaw N β H))
      (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous)
      (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous)
      (smoothGraphCore (show 1 ≤ N by omega) β H hH.continuous) k c := by
  let J : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous →L[ℝ] Lp ℝ 2 (gibbsLaw N β H) := sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous
  have hJ : Function.Injective J := sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hH
  have he : ∀ j, J ((ContinuousLinearMap.adjoint (𝕜 := ℝ) J) (D.basis j)) =
      D.resolventEigenvalue j • D.basis j := by
    intro j
    change sphericalL2Resolvent (show 1 ≤ N by omega) β H hH.continuous (D.basis j) = _
    exact D.eigen j
  have hmono : Monotone (FormMinMax.weight D.resolventEigenvalue) := D.generator_monotone
  have hlt : FormMinMax.weight D.resolventEigenvalue k < c := hc
  exact @FormMinMax.core_trial_bound_of_eigenvalue_lt
    (Lp ℝ 2 (gibbsLaw N β H))
    (sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance J
    hJ D.basis
    D.resolventEigenvalue (fun j => (D.bounds j).1) he hmono
    _ (smoothGraphCore_dense (show 1 ≤ N by omega) β H hH.continuous) k c hlt

/-- Every actual ordered eigenvalue has precisely one density-oscillation
factor, including the constant mode and all multiplicities. -/
theorem eigenvalue_comparison (hN : 2 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    (D₀ : SphericalSpectralData hN β₀ H₀ hH₀.continuous)
    (D₁ : SphericalSpectralData hN β₁ H₁ hH₁.continuous)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) (k : ℕ) :
    D₁.eigenvalue k ≤ Real.exp (u-l)*D₀.eigenvalue k := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hC := Real.exp_pos (u-l)
  let c := D₀.eigenvalue k+ε/Real.exp (u-l)
  have hc : D₀.eigenvalue k < c := lt_add_of_pos_right _ (div_pos hε hC)
  have ht := exists_smooth_trial_above_eigenvalue hN β₀ hH₀ D₀ k c hc
  have hn := eigenvalue_le_of_trial hN β₁ hH₁ D₁ k _
    (core_trial_transfer (show 1 ≤ N by omega) β₀ β₁ hH₀ hH₁ hl hu k c ht)
  convert hn using 1
  dsimp [c]
  field_simp

/-- The comparison uses spectral data actually constructed from each
Gibbs form, so no spectral object is supplied as a substantive hypothesis. -/
theorem normalized_eigenvalue_comparison (hN : 2 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) (k : ℕ) :
    (normalizedSphericalSpectralData hN β₁ H₁ hH₁.continuous).eigenvalue k ≤
      Real.exp (u-l)*(normalizedSphericalSpectralData hN β₀ H₀ hH₀.continuous).eigenvalue k :=
  eigenvalue_comparison hN β₀ β₁ hH₀ hH₁ _ _ hl hu k

end
end SlowEquilibration.SphericalSpectralComparison
