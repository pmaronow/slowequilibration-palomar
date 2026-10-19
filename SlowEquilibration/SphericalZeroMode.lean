module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalKernelRigidity
public import SlowEquilibration.SphericalKernelFubini
public import SlowEquilibration.SphericalConstantSpectrum

@[expose] public section

/-!
# The actual spherical form has exactly the constant zero mode

Zero completed energy gives genuine constant smoothed moments by proved
weighted rotation integration by parts. Actual kernel Fubini and true uniform
approximation then identify the original L² function, using the proved dense
smooth core. Thus kernel simplicity is a conclusion about the actual form.
-/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalAging.HardSphereDynamics
open scoped InnerProductSpace Topology ContDiff

/-- True zero completed spherical energy forces the actual Gibbs L² value
to be a genuine constant, in all positive spherical dimensions. -/
theorem sphericalCompletedDirichlet_zero_implies_constant {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous)
    (hE : sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH.continuous u u = 0) :
    ∃ c : ℝ, sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u =
      gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c := by
  letI := gibbsLaw_probability (show 1 ≤ N by omega) β hH.continuous
  let f := sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u
  let w := gibbsUnweightedDensity β H f
  have hw : Integrable w (gibbsLaw N β H) :=
    gibbsUnweightedDensity_integrable (show 1 ≤ N by omega) β H hH.continuous f
  have hπ : ∀ᵐ x ∂gibbsLaw N β H, OnSphere x :=
    (gibbsLaw_support (show 1 ≤ N by omega) β H).mono (fun x hx => (onSphere_iff_norm_sq x).mpr hx)
  let c := ∫ x, w x ∂gibbsLaw N β H
  have htest (g : Vector N → ℝ) (hg : ContDiff ℝ ∞ g) :
      inner ℝ f (gibbsToL2 (show 1 ≤ N by omega) β H hH.continuous g hg.continuous) =
        inner ℝ (gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c)
          (gibbsToL2 (show 1 ≤ N by omega) β H hH.continuous g hg.continuous) := by
    let p : Vector N → ℝ := fun x => gibbsDensity N β H x * g x
    have hp : Continuous p := (gibbsDensity_continuous β hH.continuous).mul hg.continuous
    have hs := sphericalSmoothObservable_weighted_tendsto (show 1 ≤ N by omega)
      (gibbsLaw N β H) hπ hw hp
    have he (n : ℕ) : (∫ x, w x*sphericalSmoothObservable (show 1 ≤ N by omega)
          (1 / ((n : ℝ) + 1)) p x ∂gibbsLaw N β H) =
        c * (∫ x, p x ∂sphereLaw N) := by
      obtain ⟨a, ha⟩ := zero_energy_smoothed_constant hN β hH u hE
        (ε := 1 / ((n : ℝ) + 1)) (by positivity)
      exact sphericalSmoothObservable_weighted_of_constant (show 1 ≤ N by omega)
        (gibbsLaw N β H) hπ hw hp _ a ha
    have heq : (∫ x, w x*p x ∂gibbsLaw N β H) = c * (∫ x, p x ∂sphereLaw N) := by
      apply tendsto_nhds_unique hs
      simpa only [he] using (tendsto_const_nhds (x := c * ∫ x, p x ∂sphereLaw N))
    have hl : (∫ x, w x*p x ∂gibbsLaw N β H) =
        inner ℝ f (gibbsToL2 (show 1 ≤ N by omega) β H hH.continuous g hg.continuous) := by
      rw [gibbsToL2_inner_right]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        dsimp [w, gibbsUnweightedDensity, p]
        field_simp [(gibbsDensity_pos (show 1 ≤ N by omega) β hH.continuous x).ne'])
    have hr : c * (∫ x, p x ∂sphereLaw N) =
        inner ℝ (gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c)
          (gibbsToL2 (show 1 ≤ N by omega) β H hH.continuous g hg.continuous) := by
      rw [gibbsConstant, gibbsToL2_inner, integral_const_mul, integral_gibbsLaw (show 1 ≤ N by omega) β hH.continuous]
    exact hl.symm.trans (heq.trans hr)
  refine ⟨c, ?_⟩
  have hz (g : Vector N → ℝ) (hg : ContDiff ℝ ∞ g) :
      inner ℝ (f - gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c)
        (gibbsToL2 (show 1 ≤ N by omega) β H hH.continuous g hg.continuous) = 0 := by
    rw [inner_sub_left, htest g hg, sub_self]
  have hzero : f - gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact (gibbsToL2_smooth_dense (show 1 ≤ N by omega) β H hH.continuous).induction_on
      (p := fun v => inner ℝ (f - gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c) v = 0)
      (f - gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      (fun g => hz g.val g.property)
  exact sub_eq_zero.mp hzero

/-- Exact characterization of the actual completed form's zero energy. -/
theorem sphericalCompletedDirichlet_zero_iff_constant {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous) :
    sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH.continuous u u = 0 ↔
      ∃ c : ℝ, sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u =
        gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c := by
  constructor
  · exact sphericalCompletedDirichlet_zero_implies_constant hN β hH u
  · rintro ⟨c, hc⟩
    let g : smoothCore N := ⟨fun _ => c, by change ContDiff ℝ ∞ (fun _ : Vector N => c); exact contDiff_const⟩
    have hu : u = smoothEnergyToGraph (show 1 ≤ N by omega) β H hH.continuous g := by
      apply sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hH
      exact hc
    rw [hu, sphericalCompletedDirichlet_smooth_energy]
    change dirichletEnergy N β H (fun _ => c) = 0
    simp [dirichletEnergy, dirichletForm, surfaceGradient_const]

/-- The genuine actual resolvent's one-eigenspace is precisely the constants. -/
theorem sphericalL2Resolvent_fixed_iff_constant {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    sphericalL2Resolvent (show 1 ≤ N by omega) β H hH.continuous f = f ↔
      ∃ c : ℝ, f = gibbsConstant (show 1 ≤ N by omega) β H hH.continuous c := by
  constructor
  · intro hf
    let u := sphericalWeakSolution (show 1 ≤ N by omega) β H hH.continuous f
    have hu : sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u = f := hf
    have hs := sphericalWeakSolution_spec (show 1 ≤ N by omega) β H hH.continuous f u
    change sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH.continuous u u +
      inner ℝ (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u)
        (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u) =
      inner ℝ f (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u) at hs
    rw [hu] at hs
    have hE : sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH.continuous u u = 0 := by linarith
    obtain ⟨c, hc⟩ := sphericalCompletedDirichlet_zero_implies_constant hN β hH u hE
    exact ⟨c, hu.symm.trans hc⟩
  · rintro ⟨c, rfl⟩
    exact sphericalL2Resolvent_constant (show 1 ≤ N by omega) β H hH c

end
end SlowEquilibration.SphericalForm
