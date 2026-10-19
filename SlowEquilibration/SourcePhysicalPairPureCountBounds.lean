-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCountBounds

/-! Actual ordered critical-pair count upper bounds, obtained by monotonicity
on the genuine sphere product probability measure. All windows are literal
physical score/value windows; constants are selected before the dimension. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalPairMarkedWindows
open SphericalPairChartKacRice SphericalPairCountGluing SphereChartVolume
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 900000

lemma source_pure_minDegree_ge_four (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) :
    4 ≤ (FiniteMixture.pure p (by omega) alpha halpha).minDegree:=by
  simpa [FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne'] using hp

theorem source_pure_actual_central_pair_count_bound (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap α:ℝ}
    (hQ:0<Q)
    (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (K:Set ℝ),MeasurableSet K →
      (∀ h∈K,|h| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h) →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,actualSpherePairCount (n+2) c (pairRadius μ hQ (source_pure_minDegree_ge_four p hp alpha halpha))
        (actualValuePairWindowMark c K (((n+3:ℕ):ℝ)^(-α)) (fun _ _=>1)) J
        ∂disorderLaw (n+3) μ.maxDegree) ≤
        ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)))*
          (∫⁻ J,actualValueWindowCount (n+2) c K (fun _ _=>1) J
            ∂disorderLaw (n+3) μ.maxDegree)^2 :=by
  dsimp only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hd:4 ≤ μ.minDegree:=source_pure_minDegree_ge_four p hp alpha halpha
  obtain ⟨C,hC,hBounds⟩:=source_pure_central_pair_window_bound p hp alpha halpha hQ hM hgap hα
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hCut:∀ᶠ n:ℕ in atTop,((n+3:ℕ):ℝ)^(-α) ≤ pairRadius μ hQ (source_pure_minDegree_ge_four p hp alpha halpha):=
    (((tendsto_rpow_neg_atTop (show 0<α by linarith)).comp hN).eventually
      (gt_mem_nhds (pairRadius_pos μ hQ hd))).mono (fun _ h=>h.le)
  refine ⟨C,hC,?_⟩
  filter_upwards [hBounds,hCut] with n hn hcut
  intro K hK hmarks
  rw [source_value_actual_pair_window_count_identity n μ hQ hd hcut K hK (fun _ _=>1) measurable_const]
  apply sphere_pair_integral_central_bound
  intro x y hx hy hr
  exact hn x y hx hy hr.le K hK hmarks

theorem source_pure_actual_subcritical_pair_count_bound (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap α:ℝ}
    (hQ:0<Q)
    (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ δ C:ℝ,0<δ ∧ δ ≤ 1 ∧ δ ≤ pairRadius μ hQ (source_pure_minDegree_ge_four p hp alpha halpha) ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (K:Set ℝ),MeasurableSet K →
      (∀ h∈K,|h| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h) →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,actualSpherePairCount (n+2) c (pairRadius μ hQ (source_pure_minDegree_ge_four p hp alpha halpha))
        (actualValuePairWindowMark c K δ (fun _ _=>1)) J ∂disorderLaw (n+3) μ.maxDegree) ≤
        ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)+
          Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)))*
          (∫⁻ J,actualValueWindowCount (n+2) c K (fun _ _=>1) J
            ∂disorderLaw (n+3) μ.maxDegree)^2 :=by
  dsimp only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hd:4 ≤ μ.minDegree:=source_pure_minDegree_ge_four p hp alpha halpha
  obtain ⟨C,hC,hCentral⟩:=source_pure_central_pair_window_bound p hp alpha halpha hQ hM hgap hα
  obtain ⟨δ0,D,hδ0,hδOne,hD,hLocal⟩:=source_pure_subcritical_pair_window_bound p hp alpha halpha hQ hM hgap
  obtain ⟨T,hT,hTail⟩:=source_sphere_pair_annulus_lintegral_rate α
  let δ:=min δ0 (pairRadius μ hQ (source_pure_minDegree_ge_four p hp alpha halpha))
  have hδ:0<δ:=lt_min hδ0 (pairRadius_pos μ hQ hd)
  have hδRad:δ ≤ pairRadius μ hQ (source_pure_minDegree_ge_four p hp alpha halpha):=min_le_right _ _
  refine ⟨δ,C+D*T,hδ,(min_le_left _ _).trans hδOne,hδRad,by positivity,?_⟩
  filter_upwards [hCentral,hLocal,hTail] with n hc hl ht
  intro K hK hmarks
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let W:=(∫⁻ J,actualValueWindowCount (n+2) c K (fun _ _=>1) J ∂disorderLaw (n+3) μ.maxDegree)^2
  let E:=((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)
  let X:=Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)
  have hE:0 ≤ E:=by unfold E;positivity
  have hX:0 ≤ X:=(Real.exp_pos _).le
  change _ ≤ ENNReal.ofReal (1+(C+D*T)*(E+X))*W
  by_cases hW:W=⊤
  · have hCoeff:ENNReal.ofReal (1+(C+D*T)*(E+X))≠0:=by positivity
    rw [hW,ENNReal.mul_top hCoeff]
    exact le_top
  · rw [source_value_actual_pair_window_count_identity n μ hQ hd hδRad K hK (fun _ _=>1) measurable_const]
    have hBound:=sphere_pair_integral_subcritical_bound n δ (((n+3:ℕ):ℝ)^(-α))
      (fun p=>intrinsicValuePairWindowIntensity c p.1 p.2 K (fun _=>1))
      (ENNReal.ofReal (1+C*E)) (ENNReal.ofReal D) W hW
      (fun x y hx hy hr=>hc x y hx hy hr K hK hmarks) (fun x y hx hy hr=>by
        have hh:=hl x y hx hy (hr.le.trans (min_le_left _ _)) K hK hmarks
        simpa only [ENNReal.ofReal_mul hD.le] using hh)
    refine hBound.trans ?_
    refine mul_le_mul_left ?_ W
    calc
      _ ≤ ENNReal.ofReal (1+C*E)+ENNReal.ofReal D*ENNReal.ofReal (T*X):=by
        exact add_le_add le_rfl (mul_le_mul_right ht _)
      _ ≤ _:=pair_count_real_coefficient_le hE hX hC.le hD.le hT.le


end
end SlowEquilibration.PairConditionalDeterminantMoments
