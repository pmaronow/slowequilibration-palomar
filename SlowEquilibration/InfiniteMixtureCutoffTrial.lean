-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCutoffCuspRoots
public import SlowEquilibration.InfiniteMixtureCuspCollar
public import SlowEquilibration.PlantedCollarGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Continuity of the actual finite planted trial pressure, including its
moving `qStar` endpoint, under the nonnegative source cutoffs. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (μ : InfiniteMixture)

theorem basedCutoff_xi_tendstoUniformlyOn (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    TendstoUniformlyOn (fun n => (μ.basedCutoff P₀ h₀ n).xi) μ.xi atTop (Icc (-1:ℝ) 1) := by
  have h := tendstoUniformlyOn_tsum_nat (f := fun p (r : ℝ) => μ.coeff p*r^p)
    (s := Icc (-1:ℝ) 1) μ.summable_coeff
    (fun p r hr => μ.norm_power_term_le (abs_le.mpr hr) p)
  have hh : Tendsto (fun n => P₀+n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      (by simpa [Nat.add_comm] using tendsto_add_atTop_nat P₀)
  have ht : TendstoUniformlyOn
      (fun n r => ∑ p ∈ Finset.range (P₀+n+1), μ.coeff p*r^p) μ.xi atTop (Icc (-1:ℝ) 1) :=
    fun v hv => hh.eventually (h v hv)
  exact ht.congr (Eventually.of_forall (fun n r _ => (μ.finiteCutoff_xi _ _ r).symm))

/-- The true finite trial pressure converges at every convergent sequence of
physical overlaps in the interior; the endpoint may depend on the cutoff. -/
theorem basedCutoff_trial_tendsto (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    (β : ℝ) {r : ℝ} {rₙ : ℕ → ℝ} (hr : r ∈ Ioo (0:ℝ) 1)
    (ht : Tendsto rₙ atTop (𝓝 r)) :
    Tendsto (fun n => SphericalModel.plantedProfileTrial (μ.basedCutoff P₀ h₀ n) β (rₙ n))
      atTop (𝓝 (μ.cuspTrialPressure β r)) := by
  have hi : r ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hr.1],hr.2.le⟩
  have hwithin : Tendsto rₙ atTop (𝓝[Icc (-1:ℝ) 1] r) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,(ht.eventually (Ioo_mem_nhds (by linarith [hr.1]) hr.2)).mono
      (fun _ hh => ⟨hh.1.le,hh.2.le⟩)⟩
  have hξ := (μ.basedCutoff_xi_tendstoUniformlyOn P₀ h₀).tendsto_comp
    (μ.continuousOn_xi r hi) hwithin
  have hξ1 := (μ.basedCutoff_xi_tendstoUniformlyOn P₀ h₀).tendsto_at
    (show (1:ℝ) ∈ Icc (-1:ℝ) 1 by norm_num)
  have hlog := (tendsto_const_nhds.sub ht).log (by linarith [hr.2] : (1:ℝ)-r ≠ 0)
  exact ((((hξ1.add hξ).const_mul (β^2)).add ht).add hlog).div_const 2

namespace CuspCoordinate
variable {μ} (c : CuspCoordinate μ)

theorem epsilonTemperature_window_eventually
    (hgap : Thresholds.dynamicalThreshold μ.xi < Thresholds.staticThreshold μ.xi) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Thresholds.dynamicalThreshold μ.xi < c.epsilonTemperature ε ∧
      c.epsilonTemperature ε < Thresholds.staticThreshold μ.xi := by
  have hc : ContinuousAt c.epsilonTemperature 0 := by
    unfold epsilonTemperature
    fun_prop
  have hv : c.epsilonTemperature 0 = Thresholds.dynamicalThreshold μ.xi := by
    simp [epsilonTemperature]
  have hs := hc.eventually (Iio_mem_nhds (by rwa [hv]))
  have hd : 0 < Thresholds.dynamicalThreshold μ.xi :=
    Real.sqrt_pos.mpr (inv_pos.mpr μ.Amax_pos)
  filter_upwards [self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds hs] with ε hε hs
  change 0 < ε at hε
  refine ⟨?_,hs⟩
  have hroot : 1 < Real.sqrt (1+ε) := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith
  change _ < Thresholds.dynamicalThreshold μ.xi * _
  nlinarith

theorem basedCutoff_trial_qStar_tendsto_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Tendsto (fun n => SphericalModel.plantedProfileTrial (μ.basedCutoff P₀ h₀ n)
        (c.epsilonTemperature ε)
        (Thresholds.qStar (μ.basedCutoff P₀ h₀ n).xi (c.epsilonTemperature ε)))
        atTop (𝓝 (μ.cuspTrialPressure (c.epsilonTemperature ε)
          (Thresholds.qStar μ.xi (c.epsilonTemperature ε)))) := by
  filter_upwards [c.epsilon_roots_eventually,c.basedCutoff_qStar_tendsto_eventually P₀ h₀]
    with ε he ht
  rw [he.2.2.2.2.2.2]
  exact μ.basedCutoff_trial_tendsto P₀ h₀ _ he.2.2.2.1 ht

theorem basedCutoff_collarCost_tendsto_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Tendsto (fun n =>
        SphericalModel.plantedProfileTrial (μ.basedCutoff P₀ h₀ n) (c.epsilonTemperature ε) (c.collarRight ε) -
        SphericalModel.plantedProfileTrial (μ.basedCutoff P₀ h₀ n) (c.epsilonTemperature ε) (c.qMinus ε))
        atTop (𝓝 (c.collarCost ε)) := by
  filter_upwards [c.collar_eventually,c.epsilon_roots_eventually] with ε hc he
  have hr : c.collarRight ε ∈ Ioo (0:ℝ) 1 :=
    ⟨he.2.2.1.1.trans (hc.1.trans hc.2.1),hc.2.2.1.trans he.2.2.2.1.2⟩
  exact (μ.basedCutoff_trial_tendsto P₀ h₀ _ hr tendsto_const_nhds).sub
    (μ.basedCutoff_trial_tendsto P₀ h₀ _ he.2.2.1 tendsto_const_nhds)

/-- Convergence of the finite module's literal geometric collar gap. -/
theorem basedCutoff_collarGap_tendsto_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Tendsto (fun n => SphericalModel.plantedCollarGap (μ.basedCutoff P₀ h₀ n)
        (c.epsilonTemperature ε) (c.collarRight ε)) atTop (𝓝 (c.collarGap ε)) := by
  filter_upwards [c.collar_eventually,c.epsilon_roots_eventually,
    c.basedCutoff_trial_qStar_tendsto_eventually P₀ h₀] with ε hc he ht
  have hr : c.collarRight ε ∈ Ioo (0:ℝ) 1 :=
    ⟨he.2.2.1.1.trans (hc.1.trans hc.2.1),hc.2.2.1.trans he.2.2.2.1.2⟩
  simpa only [SphericalModel.plantedCollarGap_eq,collarGap] using
    ht.sub (μ.basedCutoff_trial_tendsto P₀ h₀ _ hr tendsto_const_nhds)

/-- The sharp source barrier survives an actual finite cutoff at each fixed
small epsilon, with arbitrary prescribed relative loss. -/
theorem basedCutoff_collarGap_lower_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      (1-θ)*(c.barrierCoefficient*ε^(1+((2*c.m:ℕ):ℝ)⁻¹)) <
        SphericalModel.plantedCollarGap (μ.basedCutoff P₀ h₀ n)
          (c.epsilonTemperature ε) (c.collarRight ε) := by
  filter_upwards [c.basedCutoff_collarGap_tendsto_eventually P₀ h₀,
    c.collarGap_lower_eventually hθ] with ε ht hg
  exact ht.eventually (Ioi_mem_nhds hg)

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
