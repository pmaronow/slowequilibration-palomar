-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCountBounds

/-! The actual mixed pair-count estimate with its local overlap cutoff
chosen before the mesoscopic exponent.  The local intensity theorem has no
`α` input; only the central and annulus constants depend on `α`. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Filter Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalPairCountGluing
open SphericalPairChartKacRice
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_mixed_actual_subcritical_pair_cutoff_before_alpha
    (μ : FiniteMixture) {Q M gap : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hM : 0 ≤ M) (hgap : 0 < gap) :
    ∃ cut : ℝ, 0 < cut ∧ cut ≤ 1 ∧ cut ≤ pairRadius μ hQ hd ∧
      ∀ {α : ℝ}, 1/4 < α → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
          (∀ b ∈ K, |b 0| ≤ M ∧ |b 1| ≤ M ∧
            2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ b 1) →
          let c := centerCoefficients (mixtureCoefficients μ) Q
          (∫⁻ J, actualSpherePairCount (n+2) c (pairRadius μ hQ hd)
            (actualMixedPairWindowMark c K cut (fun _ _ => 1)) J
            ∂disorderLaw (n+3) μ.maxDegree) ≤
            ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+
              1/Real.sqrt (n+3:ℕ)+
              Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4))) *
            (∫⁻ J, actualScoreWindowCount (n+2) c K (fun _ _ => 1) J
              ∂disorderLaw (n+3) μ.maxDegree)^2 := by
  obtain ⟨δ₀,D,hδ₀,hδOne,hD,hLocal⟩ :=
    source_mixed_subcritical_pair_window_bound μ hQ hnp hd hM hgap
  let cut := min δ₀ (pairRadius μ hQ hd)
  have hcut : 0 < cut := lt_min hδ₀ (pairRadius_pos μ hQ hd)
  have hcutRadius : cut ≤ pairRadius μ hQ hd := min_le_right _ _
  refine ⟨cut,hcut,(min_le_left _ _).trans hδOne,hcutRadius,?_⟩
  intro α hα
  obtain ⟨C₀,hC₀,hCentral⟩ :=
    source_mixed_central_pair_window_bound μ hQ hnp hd hM hgap hα
  obtain ⟨T,hT,hTail⟩ := source_sphere_pair_annulus_lintegral_rate α
  refine ⟨C₀+D*T,by positivity,?_⟩
  filter_upwards [hCentral,hLocal,hTail] with n hc hl ht
  intro K hK hmarks
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let W := (∫⁻ J, actualScoreWindowCount (n+2) c K (fun _ _ => 1) J
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
  · rw [source_mixed_actual_pair_window_count_identity n μ hQ hd hcutRadius
      K hK (fun _ _ => 1) measurable_const]
    have hBound := sphere_pair_integral_subcritical_bound n cut
      (((n+3:ℕ):ℝ)^(-α))
      (fun p => intrinsicMixedPairWindowIntensity c p.1 p.2 K (fun _ => 1))
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
