-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothMinMax
public import SlowEquilibration.SphericalFormCore
public import SlowEquilibration.SphericalRayleighComparison
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-! The true smooth spherical form core has the same algebraic restrictions
under every positive continuous Gibbs density. The transfer below is a genuine
linear map on restrictions, not a choice of unrelated trial vectors. -/

namespace SlowEquilibration.SphericalForm
noncomputable section
open MeasureTheory Set Function
open SphericalModel SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
variable {N : ℕ}

theorem gibbsToL2_eq_zero_iff_onSphere (hN : 1 ≤ N) (β : ℝ)
    {H f : Vector N → ℝ} (hH : Continuous H) (hf : Continuous f) :
    gibbsToL2 hN β H hH f hf = 0 ↔ ∀ x, OnSphere x → f x = 0 := by
  constructor
  · intro hz
    have hae : f =ᵐ[gibbsLaw N β H] 0 := by
      have hh := (gibbsToL2_coe hN β H hH f hf).symm
      rw [hz] at hh
      exact hh.trans (Lp.coeFn_zero ℝ 2 _)
    exact continuous_eq_zero_onSphere_of_gibbs_ae hN β hH hf hae
  · intro hz
    apply Lp.ext
    filter_upwards [gibbsToL2_coe hN β H hH f hf, gibbsLaw_support hN β H,
      (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gibbsLaw N β H))] with x hfx hx hzero
    simp only [Pi.zero_apply] at hzero ⊢
    rw [hfx, hz x ((onSphere_iff_norm_sq x).mpr hx), hzero]

theorem smoothEnergyToGraph_eq_zero_iff_onSphere (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (f : smoothCore N) :
    smoothEnergyToGraph hN β H hH.continuous f = 0 ↔
      ∀ x, OnSphere x → f.val x = 0 := by
  rw [← gibbsToL2_eq_zero_iff_onSphere hN β hH.continuous (smoothCore_contDiff f).continuous]
  constructor
  · intro hz
    have hh := congrArg (sphericalEnergyL2Map hN β H hH.continuous) hz
    simpa only [sphericalEnergyL2Map_smooth, map_zero] using hh
  · intro hz
    apply sphericalEnergyL2Map_injective hN β H hH
    simpa only [sphericalEnergyL2Map_smooth, map_zero] using hz

theorem smoothEnergyToGraph_same_kernel (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁) :
    LinearMap.ker (smoothEnergyToGraph hN β₀ H₀ hH₀.continuous) =
      LinearMap.ker (smoothEnergyToGraph hN β₁ H₁ hH₁.continuous) := by
  ext f
  simp only [LinearMap.mem_ker,
    smoothEnergyToGraph_eq_zero_iff_onSphere hN β₀ hH₀,
    smoothEnergyToGraph_eq_zero_iff_onSphere hN β₁ hH₁]

/-- A true linear transfer of the same smooth restriction to a new Gibbs
form, obtained by the first isomorphism theorem and equality of null kernels. -/
def smoothCoreTransfer (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁) :
    smoothGraphCore hN β₀ H₀ hH₀.continuous →ₗ[ℝ]
      sphericalSobolevGraph hN β₁ H₁ hH₁.continuous :=
  ((LinearMap.ker (smoothEnergyToGraph hN β₀ H₀ hH₀.continuous)).liftQ
    (smoothEnergyToGraph hN β₁ H₁ hH₁.continuous)
    (smoothEnergyToGraph_same_kernel hN β₀ β₁ hH₀ hH₁).le).comp
    (smoothEnergyToGraph hN β₀ H₀ hH₀.continuous).quotKerEquivRange.symm.toLinearMap

@[simp] theorem smoothCoreTransfer_apply_image (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    (f : smoothCore N) :
    smoothCoreTransfer hN β₀ β₁ hH₀ hH₁
      ⟨smoothEnergyToGraph hN β₀ H₀ hH₀.continuous f, ⟨f, rfl⟩⟩ =
      smoothEnergyToGraph hN β₁ H₁ hH₁.continuous f := by
  change ((LinearMap.ker (smoothEnergyToGraph hN β₀ H₀ hH₀.continuous)).liftQ
    (smoothEnergyToGraph hN β₁ H₁ hH₁.continuous)
    (smoothEnergyToGraph_same_kernel hN β₀ β₁ hH₀ hH₁).le)
    ((smoothEnergyToGraph hN β₀ H₀ hH₀.continuous).quotKerEquivRange.symm
      ⟨smoothEnergyToGraph hN β₀ H₀ hH₀.continuous f, ⟨f, rfl⟩⟩) = _
  rw [(smoothEnergyToGraph hN β₀ H₀ hH₀.continuous).quotKerEquivRange_symm_apply_image]
  rfl

theorem smoothCoreTransfer_injective (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁) :
    Injective (smoothCoreTransfer hN β₀ β₁ hH₀ hH₁) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro u hu
  obtain ⟨f, hf⟩ := u.property
  have he : u = ⟨smoothEnergyToGraph hN β₀ H₀ hH₀.continuous f, ⟨f, rfl⟩⟩ :=
    Subtype.ext hf.symm
  rw [he] at hu
  have hz : smoothEnergyToGraph hN β₁ H₁ hH₁.continuous f = 0 := by
    simpa only [LinearMap.mem_ker, smoothCoreTransfer_apply_image] using hu
  have hzero := (smoothEnergyToGraph_eq_zero_iff_onSphere hN β₁ hH₁ f).mp hz
  have hfzero := (smoothEnergyToGraph_eq_zero_iff_onSphere hN β₀ hH₀ f).mpr hzero
  change u = 0
  apply Subtype.ext
  exact hf.symm.trans hfzero

theorem smooth_graph_rayleigh_eq (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (f : smoothCore N) :
    FormMinMax.rayleighQuotient (sphericalEnergyL2Map hN β H hH)
      (smoothEnergyToGraph hN β H hH f) = smoothSphereRayleigh β H f := by
  rw [FormMinMax.rayleighQuotient, formEnergy_eq_sphericalCompletedDirichlet,
    sphericalCompletedDirichlet_smooth_energy, sphericalEnergyL2Map_smooth,
    ← real_inner_self_eq_norm_sq, gibbsToL2_inner]
  simp only [smoothSphereRayleigh, pow_two]

/-- The genuine linear core transfer obeys the same single-oscillation
Rayleigh bound as its actual smooth representatives. -/
theorem smoothCoreTransfer_rayleigh_comparison (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ : Vector N → ℝ} (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u)
    (v : smoothGraphCore hN β₀ H₀ hH₀.continuous) (hv : v ≠ 0) :
    FormMinMax.rayleighQuotient (sphericalEnergyL2Map hN β₁ H₁ hH₁.continuous)
      (smoothCoreTransfer hN β₀ β₁ hH₀ hH₁ v) ≤
    Real.exp (u-l)*FormMinMax.rayleighQuotient
      (sphericalEnergyL2Map hN β₀ H₀ hH₀.continuous) v.val := by
  obtain ⟨f, hf⟩ := v.property
  have he : v = ⟨smoothEnergyToGraph hN β₀ H₀ hH₀.continuous f, ⟨f, rfl⟩⟩ :=
    Subtype.ext hf.symm
  have hf0 : smoothEnergyToGraph hN β₀ H₀ hH₀.continuous f ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact hf.symm.trans hz
  have hg0 : gibbsToL2 hN β₀ H₀ hH₀.continuous f
      (smoothCore_contDiff f).continuous ≠ 0 := by
    intro hz
    apply hf0
    apply sphericalEnergyL2Map_injective hN β₀ H₀ hH₀
    simpa only [sphericalEnergyL2Map_smooth, map_zero] using hz
  have hn : 0 < ‖gibbsToL2 hN β₀ H₀ hH₀.continuous f
      (smoothCore_contDiff f).continuous‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hnorm : ‖gibbsToL2 hN β₀ H₀ hH₀.continuous f
      (smoothCore_contDiff f).continuous‖^2 =
      unnormalizedSphereIntegral β₀ H₀ (fun x => (f.val x)^2)/partition N β₀ H₀ := by
    rw [← real_inner_self_eq_norm_sq, gibbsToL2_inner]
    have heq : (fun x => f.val x * f.val x) = (fun x => (f.val x)^2) := by
      funext x
      ring
    rw [heq]
    exact integral_gibbsLaw_eq_unnormalized hN β₀ hH₀.continuous (fun x => (f.val x)^2)
  have hm : 0 < unnormalizedSphereIntegral β₀ H₀ (fun x => (f.val x)^2) := by
    rw [hnorm] at hn
    have hp := partition_pos hN β₀ hH₀.continuous
    have hh := mul_pos hn hp
    simpa only [div_mul_cancel₀ _ hp.ne'] using hh
  rw [he, smoothCoreTransfer_apply_image, smooth_graph_rayleigh_eq,
    smooth_graph_rayleigh_eq]
  exact smoothSphereRayleigh_comparison hN β₀ β₁ hH₀.continuous hH₁.continuous
    ((smoothCore_contDiff f).of_le (by simp)) hm hl hu

end
end SlowEquilibration.SphericalForm
