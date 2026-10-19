-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorGoodCriticalPoint
public import SlowEquilibration.SphericalTaylorBandTarget
public import SlowEquilibration.SphericalTaylorPlantedBand
public import SlowEquilibration.SphericalPlantedRegularity

@[expose] public section

/-! A genuine original-field planted transverse band, with actual reference
overlap near qStar and the correct entropy-inclusive source pressure. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.SphericalForm
open scoped ENNReal Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem qStar_good_planted_transverse_band (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree)
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    ∃ q∈Ioo (Real.sqrt Q) 1,|bandOuterLatitude Q q-Q|<δ ∧
      ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
        ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ z,inner ℝ (e z) w=0) →
        disorderLaw (n+3) μ.maxDegree {J | ¬(J∈regularDisorder ∧
          ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
            plantedProfileTrial μ β Q-ε<
              transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y+
                Real.log (1-Q)/2)}≤6*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
  have hQ : Q∈Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hβ0 : 0<β := μ.dynamicalThreshold_pos.trans hβ
  obtain ⟨q,hq,hstrong,hclose,htrial⟩ := exists_strong_qStar_band_trial μ hβ hδ (show 0<ε/2 by positivity)
  have hqpos : 0<q := (Real.sqrt_pos.mpr hQ.1).trans hq.1
  have hqabs : |q|<1 := by rw [abs_of_pos hqpos]; exact hq.2
  let a := latitudeDerivativeVariance c q
  obtain ⟨α,hα,hgood⟩ := qStar_good_thermal_critical_point μ hscope hβ
    (show 0<ε/(8*β) by positivity) (show 0<ε/8 by positivity) hqpos.ne' hqabs hstrong
  let η := min 1 α
  have hη : 0<η := lt_min (by norm_num) hα
  refine ⟨q,hq,hclose,η,hη,?_⟩
  filter_upwards [hgood] with n hn
  intro w hw e he
  let Bad : Set (Disorder (n+3) μ.maxDegree) := {J | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    surfaceGradient (latitudeField c J w e q) y=0 ∧
    Real.sqrt a-ε/(8*β)<actualLatitudeScore c w e q J y 0 ∧
    F-ε/8≤transverseRemainderPressure c w e q Q β J y}
  have hsub : {J : Disorder (n+3) μ.maxDegree | ¬(J∈regularDisorder ∧
      ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧ plantedProfileTrial μ β Q-ε<
        transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y+
          Real.log (1-Q)/2)}⊆(regularDisorder (N := n+3) (P := μ.maxDegree))ᶜ∪Bad := by
    intro J hJ
    by_cases hreg : J∈regularDisorder
    · right
      intro hg
      obtain ⟨y,hy,hcrit,hheight,hthermal⟩ := hg
      have hband := good_critical_transverseBandPressure_lower (by omega) μ hQ.1 hβ0.le
        w e hqabs J y hy hcrit hheight.le hthermal
      have hid := transverseBandPressure_plantedShift (by omega) μ Q q β w hw e he J y
      have halgebra : β*(Real.sqrt a-ε/(8*β))+(F-ε/8)+β^2*μ.xi (bandOuterLatitude Q q)+
          Real.log (1-Q)/2=auxiliaryBandTrial μ β Q q-ε/4 := by
        unfold auxiliaryBandTrial
        change β*(Real.sqrt a-ε/(8*β))+(F-ε/8)+β^2*μ.xi (bandOuterLatitude Q q)+
          Real.log (1-Q)/2=β*Real.sqrt a+F+β^2*μ.xi (bandOuterLatitude Q q)+Real.log (1-Q)/2-ε/4
        field_simp [hβ0.ne']
        ring
      have hfinal : plantedProfileTrial μ β Q-ε<
          transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y+
            Real.log (1-Q)/2 := by
        rw [hid]
        have hh : auxiliaryBandTrial μ β Q q-ε/4≤
            transverseBandPressure μ w e q Q β J y+β^2*μ.xi (bandOuterLatitude Q q)+Real.log (1-Q)/2 := by
          rw [← halgebra]
          exact add_le_add (add_le_add hband le_rfl) le_rfl
        have htr : plantedProfileTrial μ β Q-ε<auxiliaryBandTrial μ β Q q-ε/4 := by linarith
        exact htr.trans_le hh
      exact hJ ⟨hreg,y,hy,hfinal⟩
    · exact Or.inl hreg
  have hN : (0 : ℝ)≤((n+3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrate (r : ℝ) (hr : η≤r) : ENNReal.ofReal (Real.exp (-r*((n+3 : ℕ) : ℝ)))≤
      ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hr hN]
  have hreg : disorderLaw (n+3) μ.maxDegree (regularDisorder (N := n+3) (P := μ.maxDegree))ᶜ≤
      ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
    apply (regularDisorder_failure_ennreal (N := n+3) (P := μ.maxDegree) (by omega)).trans
    simpa only [neg_mul,one_mul] using hrate 1 (min_le_left _ _)
  have hb : disorderLaw (n+3) μ.maxDegree Bad≤5*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
    apply (hn w hw e he).trans
    simpa only [mul_comm] using mul_le_mul_left (hrate α (min_le_right _ _)) 5
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ)))+
        5*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := add_le_add hreg hb
    _ = _ := by ring

end
end SlowEquilibration.SphericalTaylorRemainder
