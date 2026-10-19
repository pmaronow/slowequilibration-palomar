-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPureCountBounds

/-! In the pure value-mark model, the actual subcritical pair cutoff comes
from the local estimate before the mesoscopic exponent. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Filter Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalPairCountGluing SphericalPairChartKacRice SphericalPairMarkedWindows
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_pure_actual_subcritical_pair_cutoff_before_alpha
    (p : ℕ) (hp : 4 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q M gap : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M) (hgap : 0 < gap) :
    let μ := FiniteMixture.pure p (by omega) a ha
    ∃ cut : ℝ, 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ hQ (source_pure_minDegree_ge_four p hp a ha) ∧
      ∀ {α : ℝ}, 1/4 < α → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ K : Set ℝ, MeasurableSet K →
          (∀ h ∈ K, |h| ≤ M ∧
            2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h) →
          let c := centerCoefficients (mixtureCoefficients μ) Q
          (∫⁻ J, actualSpherePairCount (n+2) c
            (pairRadius μ hQ (source_pure_minDegree_ge_four p hp a ha))
            (actualValuePairWindowMark c K cut (fun _ _ => 1)) J
            ∂disorderLaw (n+3) μ.maxDegree) ≤
            ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+
              1/Real.sqrt (n+3:ℕ)+
              Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4))) *
            (∫⁻ J, actualValueWindowCount (n+2) c K (fun _ _ => 1) J
              ∂disorderLaw (n+3) μ.maxDegree)^2 := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) a ha
  have hd : 4 ≤ μ.minDegree := source_pure_minDegree_ge_four p hp a ha
  obtain ⟨δ₀,D,hδ₀,hδOne,hD,hLocal⟩ :=
    source_pure_subcritical_pair_window_bound p hp a ha hQ hM hgap
  let cut := min δ₀ (pairRadius μ hQ hd)
  have hcut : 0 < cut := lt_min hδ₀ (pairRadius_pos μ hQ hd)
  have hcutRad : cut ≤ pairRadius μ hQ hd := min_le_right _ _
  refine ⟨cut,hcut,(min_le_left _ _).trans hδOne,hcutRad,?_⟩
  intro α hα
  obtain ⟨C₀,hC₀,hCentral⟩ :=
    source_pure_central_pair_window_bound p hp a ha hQ hM hgap hα
  obtain ⟨T,hT,hTail⟩ := source_sphere_pair_annulus_lintegral_rate α
  refine ⟨C₀+D*T,by positivity,?_⟩
  filter_upwards [hCentral,hLocal,hTail] with n hc hl ht
  intro K hK hmarks
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let W := (∫⁻ J, actualValueWindowCount (n+2) c K (fun _ _ => 1) J
    ∂disorderLaw (n+3) μ.maxDegree)^2
  let E := ((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)
  let X := Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)
  have hE : 0 ≤ E := by unfold E; positivity
  have hX : 0 ≤ X := (Real.exp_pos _).le
  change _ ≤ ENNReal.ofReal (1+(C₀+D*T)*(E+X))*W
  by_cases hW : W = ⊤
  · have hCoeff : ENNReal.ofReal (1+(C₀+D*T)*(E+X)) ≠ 0 := by positivity
    rw [hW,ENNReal.mul_top hCoeff]
    exact le_top
  · rw [source_value_actual_pair_window_count_identity n μ hQ hd hcutRad
      K hK (fun _ _ => 1) measurable_const]
    have hBound := sphere_pair_integral_subcritical_bound n cut
      (((n+3:ℕ):ℝ)^(-α))
      (fun p => intrinsicValuePairWindowIntensity c p.1 p.2 K (fun _ => 1))
      (ENNReal.ofReal (1+C₀*E)) (ENNReal.ofReal D) W hW
      (fun x y hx hy hr => hc x y hx hy hr K hK hmarks)
      (fun x y hx hy hr => by
        have hh := hl x y hx hy (hr.le.trans (min_le_left _ _)) K hK hmarks
        simpa only [ENNReal.ofReal_mul hD.le] using hh)
    refine hBound.trans ?_
    refine mul_le_mul_left ?_ W
    calc
      _ ≤ ENNReal.ofReal (1+C₀*E)+ENNReal.ofReal D*ENNReal.ofReal (T*X) := by
        exact add_le_add le_rfl (mul_le_mul_right ht _)
      _ ≤ _ := pair_count_real_coefficient_le hE hX hC₀.le hD.le hT.le

end
end SlowEquilibration.PairConditionalDeterminantMoments
