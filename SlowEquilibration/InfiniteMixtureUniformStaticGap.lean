-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCutoffThreshold
public import SlowEquilibration.PlantedTrialGeometry

/-! A single actual far-overlap trial-pressure gap controls every finite
cutoff and every temperature in a fixed substatic interval. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem xi_monotoneOn_nonnegative (μ : InfiniteMixture) : MonotoneOn μ.xi (Icc 0 1) := by
  intro r hr s hs hrs
  apply (μ.summable_xi (abs_le.mpr ⟨by linarith [hr.1],hr.2⟩)).tsum_le_tsum _
    (μ.summable_xi (abs_le.mpr ⟨by linarith [hs.1],hs.2⟩))
  intro p
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hrs p) (μ.nonneg p)

/-- No right-endpoint cutoff enters this positive gap. Consequently choosing a
pole cutoff later cannot shrink the exponent. -/
theorem exists_uniform_finiteCutoff_trial_gap (μ : InfiniteMixture)
    {β₀ δ : ℝ} (hβ₀ : 0<β₀) (hβs : β₀<Thresholds.staticThreshold μ.xi)
    (hδ : δ∈Ioo (0:ℝ) 1) :
    ∃ η : ℝ,0<η ∧ ∀ P (hP : ∃ p,p≤P ∧ 0<μ.coeff p),∀ β : ℝ,
      0≤β → β≤β₀ → ∀ q∈Ico δ 1,
        SphericalModel.plantedProfileTrial (μ.finiteCutoff P hP) β q≤
          β^2*(μ.finiteCutoff P hP).xi 1/2-η := by
  obtain ⟨β₁,hβ₁,hβ₁s⟩ := exists_between hβs
  let η : ℝ := (β₁^2-β₀^2)*μ.xi δ/2
  have hd : 0<β₁^2-β₀^2 := by nlinarith
  have hη : 0<η := div_pos (mul_pos hd (μ.xi_pos hδ)) (by norm_num)
  refine ⟨η,hη,?_⟩
  intro P hP β hβ hβle q hq
  have hqi : q∈Ioo (0:ℝ) 1 := ⟨hδ.1.trans_le hq.1,hq.2⟩
  have hPhi := Thresholds.Phi_neg_of_lt_staticThreshold (fun r hr => μ.xi_pos hr)
    (show 0≤β₁ by linarith) hβ₁s q hqi
  have hxq := μ.xi_pos hqi
  have hxδ := μ.xi_monotoneOn_nonnegative ⟨hδ.1.le,hδ.2.le⟩ ⟨hqi.1.le,hqi.2.le⟩ hq.1
  have hmul := mul_le_mul_of_nonneg_left hxδ hd.le
  have hsq : β^2≤β₀^2 := by nlinarith
  have hcv : β^2*(μ.finiteCutoff P hP).xi q≤β₀^2*μ.xi q := by
    exact (mul_le_mul_of_nonneg_left (μ.finiteCutoff_xi_le P hP ⟨hqi.1.le,hqi.2.le⟩)
      (sq_nonneg β)).trans (mul_le_mul_of_nonneg_right hsq hxq.le)
  rw [SphericalModel.plantedProfileTrial_eq_annealed_add_Phi]
  unfold Thresholds.Phi at hPhi ⊢
  dsimp [η]
  nlinarith

theorem finiteCutoff_temperature_variance_le (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) {β β₀ : ℝ} (hβ : 0≤β) (hβle : β≤β₀) :
    β^2*(μ.finiteCutoff P hP).xi 1≤β₀^2*μ.xi 1 := by
  have hξ := μ.finiteCutoff_xi_le P hP (r := 1) (by norm_num)
  have hsq : β^2≤β₀^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hξ (sq_nonneg β)).trans
    (mul_le_mul_of_nonneg_right hsq (tsum_nonneg fun p => by simp [μ.nonneg p]))

end SlowEquilibration.InfiniteMixture
