-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCapFrame
public import SlowEquilibration.SphericalNormalizedBasis

/-!
# Exact counting with the literal continuum cap frame

This proves the deterministic `lem:inf-frame` for the actual spherical
Gibbs gradient form of an arbitrary C¹ potential (hence every C² potential
in the source). The actual basis is constructed internally. The cap, inner
cap and collar hypotheses are the source inputs, not spectral conclusions.
-/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalCapFrameCount

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalCapCutoff SphericalCapFrame
open SphericalLaplaceIdentification SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal ENNReal

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

/-- The source r_N, with its exact numerical prefactor. -/
def energyRatio (N : ℕ) (q₁ q₂ barrier δ : ℝ) : ℝ :=
  collarCoefficient N q₁ q₂ * Real.exp (-(N : ℝ) * (barrier - 4 * δ))

/-- The literal finite set of eigenvalue indices below Λ in the true
normalized ordered spectral data; multiplicity is recorded by the indices. -/
def cutoffIndices (hN : 2 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (Λ : ℝ) : Finset ℕ :=
  (SpectralRank.cutoff_indices_finite (normalizedSphericalSpectralData hN β H hH).eigenvalue
    (normalizedSphericalSpectralData hN β H hH).generator_tendsto_atTop Λ).toFinset

lemma mem_cutoffIndices (hN : 2 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (Λ : ℝ) (j : ℕ) :
    j ∈ cutoffIndices hN β H hH Λ ↔
      (normalizedSphericalSpectralData hN β H hH).eigenvalue j ≤ Λ := by
  simp only [cutoffIndices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- Full literal continuum cap-indicator count in `lem:inf-frame`,
including the cancellation of the core exponent from the mode-count rate. -/
theorem cap_indicator_count (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hHC : ContDiff ℝ 1 H)
    (G : Set (Vector N)) (hG : MeasurableSet G)
    {q₁ q₂ J barrier δ c Λ : ℝ} (hq : q₁ < q₂)
    (hMass : 1 / 2 ≤ (gibbsLaw N β H).real G)
    (hOuter : ∀ u ∈ G, (gibbsLaw N β H).real (cap u q₁) ≤ Real.exp (-(N : ℝ) * (J - 2 * δ)))
    (hInner : ∀ u ∈ G, Real.exp (-(N : ℝ) * (J + 2 * δ)) ≤ (gibbsLaw N β H).real (cap u q₂))
    (hCollar : ∀ u ∈ G, (gibbsLaw N β H).real (collar u q₁ q₂) ≤
      Real.exp (-(N : ℝ) * (J + barrier - 2 * δ)))
    (hColumn : ∀ x, OnSphere x → (gibbsLaw N β H).real (cap x q₁) ≤ Real.exp (-c * N))
    (hΛ : energyRatio N q₁ q₂ barrier δ < Λ) :
    (1 - energyRatio N q₁ q₂ barrier δ / Λ) * (1 / 2) * Real.exp ((N : ℝ) * (c - 4 * δ)) ≤
      ((cutoffIndices hN β H hHC.continuous Λ).card : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  let π := gibbsLaw N β H
  let _ := gibbsLaw_probability hN1 β hHC.continuous
  let ν := π.restrict G
  let D := normalizedSphericalSpectralData hN β H hHC.continuous
  let f := capTrial (N := N) q₁ q₂
  let u (a : Vector N) := C1ToGraph hN1 β H hHC.continuous (f a)
    ((capTrial_contDiff q₁ q₂ a).of_le (by simp))
  let F : Vector N → Lp ℝ 2 π := fun a =>
    gibbsToL2 hN1 β H hHC.continuous (f a) (capTrial_contDiff q₁ q₂ a).continuous
  have hrep (a : Vector N) : f a =ᵐ[π] F a :=
    (gibbsToL2_coe hN1 β H hHC.continuous (f a) (capTrial_contDiff q₁ q₂ a).continuous).symm
  have hFnorm (a : Vector N) : ‖F a‖^2 = squareMass β H q₁ q₂ a := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (gibbsToL2 hN1 β H hHC.continuous (f a) _) _ = _
    rw [gibbsToL2_inner]
    unfold squareMass
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp [f]; ring)
  have hνsphere : ∀ᵐ a ∂ν, OnSphere a :=
    (ae_restrict_of_ae (gibbsLaw_support hN1 β H)).mono
      (fun a ha => (onSphere_iff_norm_sq a).mpr ha)
  have hνG : ∀ᵐ a ∂ν, a ∈ G := ae_restrict_mem hG
  have hmass : Integrable (fun a => ‖F a‖^2) ν := by
    simp_rw [hFnorm]
    exact squareMass_integrable hN1 β hHC.continuous q₁ q₂ ν
  have hEeq : spectralFrameEnergy D.basis D.eigenvalue F =
      (fun a => dirichletEnergy N β H (f a)) := by
    funext a
    calc
      _ = sphericalCompletedDirichlet hN1 β H hHC.continuous (u a) (u a) :=
        D.energy_eq_completed hHC (u a)
      _ = _ := sphericalCompletedDirichlet_C1_energy hN1 β H hHC.continuous (f a) _
  have hEI : Integrable (spectralFrameEnergy D.basis D.eigenvalue F) ν := by
    rw [hEeq]
    exact capTrial_energy_integrable hN1 β hHC.continuous hq ν hνsphere
  have hK : 0 ≤ collarCoefficient N q₁ q₂ := by dsimp [collarCoefficient]; positivity
  have hr : 0 ≤ energyRatio N q₁ q₂ barrier δ := mul_nonneg hK (Real.exp_pos _).le
  have hT : π.real G * Real.exp (-(N : ℝ) * (J + 2 * δ)) ≤ ∫ a, ‖F a‖^2 ∂ν := by
    have ht := integral_mono_ae (integrable_const (Real.exp (-(N : ℝ) * (J + 2 * δ)))) hmass (by
      filter_upwards [hνG] with a ha
      rw [hFnorm]
      exact (hInner a ha).trans (capTrial_square_mass_lower hN1 β hHC.continuous hq a))
    simpa only [integral_const, ν, measureReal_restrict_apply_univ, smul_eq_mul] using ht
  have hEupper : (∫ a, spectralFrameEnergy D.basis D.eigenvalue F a ∂ν) ≤
      π.real G * collarCoefficient N q₁ q₂ * Real.exp (-(N : ℝ) * (J + barrier - 2 * δ)) := by
    rw [hEeq]
    have ht := integral_mono_ae (capTrial_energy_integrable hN1 β hHC.continuous hq ν hνsphere)
      (integrable_const (collarCoefficient N q₁ q₂ * Real.exp (-(N : ℝ) * (J + barrier - 2 * δ)))) (by
      filter_upwards [hνG, hνsphere] with a ha hs
      exact (capTrial_energy_le_collar hN1 β hHC.continuous hq a hs).trans
        (mul_le_mul_of_nonneg_left (hCollar a ha) hK))
    simpa only [integral_const, ν, measureReal_restrict_apply_univ, smul_eq_mul, mul_assoc] using ht
  have henergy : (∫ a, spectralFrameEnergy D.basis D.eigenvalue F a ∂ν) ≤
      energyRatio N q₁ q₂ barrier δ * (∫ a, ‖F a‖^2 ∂ν) := by
    have he : energyRatio N q₁ q₂ barrier δ *
        (π.real G * Real.exp (-(N : ℝ) * (J + 2 * δ))) =
        π.real G * collarCoefficient N q₁ q₂ * Real.exp (-(N : ℝ) * (J + barrier - 2 * δ)) := by
      dsimp [energyRatio]
      calc
        _ = π.real G * collarCoefficient N q₁ q₂ *
            (Real.exp (-(N : ℝ) * (barrier - 4 * δ)) * Real.exp (-(N : ℝ) * (J + 2 * δ))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    exact hEupper.trans (he ▸ mul_le_mul_of_nonneg_left hT hr)
  have hrow : ∀ᵐ a ∂ν, (∫ x, f a x ∂π) ≤ Real.exp (-(N : ℝ) * (J - 2 * δ)) := by
    filter_upwards [hνG] with a ha
    exact (capTrial_row_le hN1 β hHC.continuous hq a).trans (hOuter a ha)
  have hcol : ∀ᵐ x ∂π, (∫⁻ a, ENNReal.ofReal (f a x) ∂ν) ≤ ENNReal.ofReal (Real.exp (-c * N)) := by
    filter_upwards [gibbsLaw_support hN1 β H] with x hx
    have hs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    have heq : (fun a => f a x) = f x := by
      funext a
      dsimp [f, capTrial, overlap]
      rw [real_inner_comm]
    have heq' : (fun a => ENNReal.ofReal (f a x)) = (fun a => ENNReal.ofReal (f x a)) :=
      congrArg (fun g : Vector N → ℝ => fun a => ENNReal.ofReal (g a)) heq
    rw [heq']
    have hi := integrable_gibbs_of_continuous hN1 β hHC.continuous (capTrial_contDiff q₁ q₂ x).continuous
    have hn : 0 ≤ᵐ[π] f x := ae_of_all _ (fun a => cutoff_nonneg q₁ q₂ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi.restrict (ae_restrict_of_ae hn)]
    apply ENNReal.ofReal_le_ofReal
    exact (integral_mono_measure Measure.restrict_le_self hn hi).trans
      ((capTrial_row_le hN1 β hHC.continuous hq x).trans (hColumn x hs))
  have hform : ∀ᵐ a ∂ν, Summable (fun j => D.eigenvalue j * (inner ℝ (D.basis j) (F a))^2) := by
    apply ae_of_all
    intro a
    exact (D.formDomain_iff hHC (F a)).mp ⟨u a, rfl⟩
  have hcount := measure_frame_spectral_count ν π D.basis F f
    (fun j => (D.basis j : Vector N → ℝ)) D.eigenvalue
    (cutoffIndices hN β H hHC.continuous Λ) (energyRatio N q₁ q₂ barrier δ) Λ
    (Real.exp (-(N : ℝ) * (J - 2 * δ))) (Real.exp (-c * N))
    (capTrial_joint_contDiff q₁ q₂).continuous.measurable
    (fun a x => cutoff_nonneg q₁ q₂ _) hrep
    (fun j => (Lp.stronglyMeasurable (D.basis j)).measurable)
    (fun j => ae_of_all _ (fun x => rfl)) (Real.exp_pos _) (Real.exp_pos _) hr hΛ hrow hcol hmass
    D.eigenvalue_nonneg (mem_cutoffIndices hN β H hHC.continuous Λ) hform hEI henergy
  have hΛpos : 0 < Λ := hr.trans_lt hΛ
  have hfactor : 0 ≤ 1 - energyRatio N q₁ q₂ barrier δ / Λ :=
    sub_nonneg.mpr ((div_le_one hΛpos).mpr hΛ.le)
  have hden : 0 < Real.exp (-(N : ℝ) * (J - 2 * δ)) * Real.exp (-c * N) := by positivity
  have halgebra : (π.real G * Real.exp (-(N : ℝ) * (J + 2 * δ))) /
      (Real.exp (-(N : ℝ) * (J - 2 * δ)) * Real.exp (-c * N)) =
      π.real G * Real.exp ((N : ℝ) * (c - 4 * δ)) := by
    rw [← Real.exp_add, mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  apply le_trans _ hcount
  calc
    _ ≤ (1 - energyRatio N q₁ q₂ barrier δ / Λ) *
        (π.real G * Real.exp ((N : ℝ) * (c - 4 * δ))) := by
      have hm := mul_le_mul_of_nonneg_right hMass (Real.exp_pos ((N : ℝ) * (c - 4 * δ))).le
      have hmul := mul_le_mul_of_nonneg_left hm hfactor
      simpa only [mul_assoc] using hmul
    _ = (1 - energyRatio N q₁ q₂ barrier δ / Λ) *
        (π.real G * Real.exp (-(N : ℝ) * (J + 2 * δ))) /
          (Real.exp (-(N : ℝ) * (J - 2 * δ)) * Real.exp (-c * N)) := by
      rw [mul_div_assoc, halgebra]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT hfactor) hden.le

end SlowEquilibration.SphericalCapFrameCount
