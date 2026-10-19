-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureAnalyticCountBound
public import SlowEquilibration.SphericalPureDenominatorScaleLower

/-! Every fixed selected-center pure critical window is eventually contained
in the manuscript's wider deterministic analytic window with any prescribed
radial neighborhood of the contact mark. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalPureDenominatorScaleLower
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 550000

theorem sourcePure_selected_window_eventually_in_analytic_window
    (p : ℕ) (hp : 2 ≤ p)
    {E c M δ L : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (m : ℕ → ℝ)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-sourcePureAnalyticCenter (j+2) E c| ≤ M)
    (U : Set ℝ) (hU : (p : ℝ)*E ∈ interior U) :
    ∀ᶠ n : ℕ in atTop,
      pureScoreWindow p
        {b : EuclideanSpace ℝ (Fin 2) |
          b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧
          b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} ⊆
      pureScoreWindow p
        (physicalEnergyWindow (n+3)
          (Icc (sourcePureAnalyticCenter (n+3) E c-(L+M))
            (sourcePureAnalyticCenter (n+3) E c+(L+M))) U) := by
  have hUnhds : U ∈ 𝓝 ((p : ℝ)*E) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hU) interior_subset
  have hf : ContinuousAt (fun e : ℝ => (p : ℝ)*e) E :=
    (continuous_const.mul continuous_id).continuousAt
  have hpre : (fun e : ℝ => (p : ℝ)*e) ⁻¹' U ∈ 𝓝 E := hf.tendsto hUnhds
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hρ2 : 0 < ρ/2 := half_pos hρ
  have hNear : Icc (E-ρ/2) (E+ρ/2) ⊆
      (fun e : ℝ => (p : ℝ)*e) ⁻¹' U := by
    intro e he
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have heAbs : |e-E| ≤ ρ/2 := abs_le.mpr (by constructor <;> linarith [he.1,he.2])
    linarith
  have hcenter' : ∀ᶠ j : ℕ in atTop,
      |m j-((j+2 : ℕ)*E-Real.log (j+2 : ℕ)/(2*c))| ≤ M := by
    simpa only [sourcePureAnalyticCenter] using hcenter
  have hBox := pure_centered_window_eventually_in_energy_box
    hc hM m hcenter' (ρ/2) hρ2 δ L
  have hshift := (tendsto_add_atTop_nat 1).eventually hcenter
  filter_upwards [hBox,hshift] with n hnBox hnCenter
  intro e he
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hwin : ((n+3 : ℕ) : ℝ)*e ∈
      Icc (m (n+1)-L) (m (n+1)+L) := by
    simpa only [pureScoreWindow,pureScoreLine,sourcePureCenteredRawNormalizedWindow,
      Set.mem_preimage,Set.mem_ofPred_eq,Matrix.cons_val_zero,
      sub_eq_add_neg] using he.1
  have hrad : (p : ℝ)*e ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ)) := by
    have hh := he.2
    change (p : ℝ)*e ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ)) at hh
    exact hh
  have hE : e ∈ Ioo (E-δ) (E+δ) := by
    exact ⟨lt_of_mul_lt_mul_left hrad.1 hp0.le,
      lt_of_mul_lt_mul_left hrad.2 hp0.le⟩
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hval : e ∈ sourcePureCenteredNormalizedWindow n m E δ (-L) L := by
    refine ⟨?_,?_⟩
    · simpa only [sourcePureCenteredNormalizedWindow,Set.mem_preimage,
        sub_eq_add_neg] using hwin
    · exact ⟨mul_lt_mul_of_pos_left hE.1 hN,
        mul_lt_mul_of_pos_left hE.2 hN⟩
  have hNearU : (p : ℝ)*e ∈ U := hNear (hnBox hval)
  have hraw := hwin
  have hdiff := abs_le.mp hnCenter
  have hEnergy : ((n+3 : ℕ) : ℝ)*e ∈
      Icc (sourcePureAnalyticCenter (n+3) E c-(L+M))
        (sourcePureAnalyticCenter (n+3) E c+(L+M)) := by
    simp only [show n+1+2=n+3 by omega] at hdiff
    constructor <;> dsimp [sourcePureAnalyticCenter] at * <;> linarith [hraw.1,hraw.2]
  change ((n+3 : ℕ) : ℝ)*e ∈
      Icc (sourcePureAnalyticCenter (n+3) E c-(L+M))
        (sourcePureAnalyticCenter (n+3) E c+(L+M)) ∧
    (p : ℝ)*e ∈ U
  exact ⟨hEnergy,hNearU⟩

end SlowEquilibration.SphericalMarkedWindows
