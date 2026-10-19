-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapExteriorTailPackage
public import SlowEquilibration.SphericalPureCapEndpointFixed

/-! A single proper-pure cap, contact band, and pole cutoff control all
fixed energy-shift windows; only prefactor bounds and dimension thresholds
depend on the chosen shift radius. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapExteriorFixedGeometry
noncomputable section
open Set Filter MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapResidualMargin SphericalPureCapSourceScalars
open SphericalPureCapAwayGap SphericalPureCapCompactTail
open SphericalPureCapEndpointFixed PureStationarity
open scoped Topology
set_option autoImplicit false

/-- The source cap cutoff `a`, contact width `b`, and pole cutoff `ε` can be
chosen before the energy-window radius `L`. -/
theorem sourcePure_cap_exterior_fixed_geometry
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀upper : Real.sqrt Q+b₀ < 1) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let E := markE μ β x Q
    let Λ := sourcePureLatitudeExponent p 1 Q β E
    let F := CSParisiMeasure.variationalValue μ β
    ∃ a b ε δ : ℝ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ b ≤ b₀ ∧
      q+b < 1-ε ∧ 0 < ε ∧ ε < 1 ∧ 0 < δ ∧
      pureResidualCoefficient p β a < 1/2 ∧
      pureIntensityConstant p (by omega) < β*a^p ∧ Λ q = F ∧
      ∀ L : ℝ, 0 ≤ L → ∃ M₁ M₂ : ℝ, ∃ N₀ : ℕ,
        0 ≤ M₁ ∧ 0 ≤ M₂ ∧
        (∀ N : ℕ, ∀ u : ℝ, u ≤ L →
          (∫ t in a..q-b, sourcePureLatitudeJacobian t *
            Real.exp ((N:ℝ)*Λ t+β*u*t^p)) ≤
              (q-b-a)*M₁*Real.exp ((N:ℝ)*(F-δ)+β*L)) ∧
        (∀ N : ℕ, ∀ u : ℝ, u ≤ L →
          (∫ t in q+b..1-ε, sourcePureLatitudeJacobian t *
            Real.exp ((N:ℝ)*Λ t+β*u*t^p)) ≤
              (1-ε-(q+b))*M₂*Real.exp ((N:ℝ)*(F-δ)+β*L)) ∧
        (∀ N ≥ N₀, 4 ≤ N → ∀ H : ℝ,
          0 ≤ H → H ≤ (N:ℝ)*pureEnergyConstant p (by omega)+L →
          (∫ t in 1-ε..1,
            (1-t^2)^(((N:ℝ)-3)/2) *
              Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
            Real.exp ((N:ℝ)*(F-1))) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let E := markE μ β x Q
  let Λ := sourcePureLatitudeExponent p 1 Q β E
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨a,haHalf,haq,hCa,hDepth,hleft,hright,hcontact,_,_⟩ :=
    sourcePure_cap_latitude_choice p hp h
  have hsc := sourcePure_certificate_scalar_coordinates p hp h
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have ha0 : 0 < a := (by positivity : 0 < 1/Real.sqrt 2).trans haHalf
  let b := min ((q-a)/2) (min b₀ ((1-q)/2))
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (by linarith [haq]) (lt_min hb₀ (by linarith [hb₀upper]))
  have hbqa : b ≤ (q-a)/2 := min_le_left _ _
  have hbb₀ : b ≤ b₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hbq1 : b ≤ (1-q)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hal : a < q-b := by linarith
  have hlq : q-b < q := by linarith
  have hqr : q < q+b := by linarith
  have hr1 : q+b < 1 := by linarith [hb₀upper]
  obtain ⟨δ,hδ,hgap⟩ := cap_exponent_gap_away_from_contact Λ
    hal.le hlq hqr hr1 hleft hright
  obtain ⟨ε,hε0,hε1,hεr,hPole⟩ :=
    exists_pure_cap_endpoint_fixed_epsilon p hp
      (β:=β) (e:=pureEnergyConstant p (by omega)) (a:=q+b) (F:=F)
      h.beta_pos ⟨(add_pos hq0 hb).le,hr1⟩
  have hleftBand : Icc a (q-b) ⊆ Ioo (-1:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ha0,ht.1],by linarith [hlq,hr1,ht.2]⟩
  have hleft01 : Icc a (q-b) ⊆ Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨ha0.le.trans ht.1,by linarith [hlq,hr1,ht.2]⟩
  have hgapLeft : ∀ t ∈ Icc a (q-b), Λ t ≤ Λ q-δ := by
    intro t ht
    exact hgap t ⟨ht.1,by linarith [hlq,hr1,ht.2]⟩ (Or.inl ht.2)
  have hrightBand : Icc (q+b) (1-ε) ⊆ Ioo (-1:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [hq0,hb,ht.1],by linarith [hε0,ht.2]⟩
  have hright01 : Icc (q+b) (1-ε) ⊆ Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [hq0,hb,ht.1],by linarith [hε0,ht.2]⟩
  have hgapRight : ∀ t ∈ Icc (q+b) (1-ε), Λ t ≤ Λ q-δ := by
    intro t ht
    exact hgap t ⟨by linarith [hal,hlq,hqr,ht.1],by linarith [hε0,ht.2]⟩
      (Or.inr ht.1)
  have hDepth' : pureIntensityConstant p (by omega) < β*a^p := by
    rw [←hsc.2]
    exact hDepth
  refine ⟨a,b,ε,δ,haHalf,hal,hb,hbb₀,hεr,hε0,hε1,hδ,
    hCa,hDepth',hcontact,?_⟩
  intro L hL
  obtain ⟨M₁,hM₁,hLeftIntegral⟩ := sourcePure_cap_compact_tail p
    h.overlap_range.1 h.beta_pos hL hal.le hleftBand hleft01 hgapLeft
  obtain ⟨M₂,hM₂,hRightIntegral⟩ := sourcePure_cap_compact_tail p
    h.overlap_range.1 h.beta_pos hL hεr.le hrightBand hright01 hgapRight
  obtain ⟨N₀,hPoleL⟩ := hPole L hL
  refine ⟨M₁,M₂,N₀,hM₁,hM₂,?_,?_,?_⟩
  · intro N u hu
    have hh := hLeftIntegral N u hu
    rw [hcontact] at hh
    simpa [q,E,μ,Λ,F] using hh
  · intro N u hu
    have hh := hRightIntegral N u hu
    rw [hcontact] at hh
    simpa [q,E,μ,Λ,F] using hh
  · intro N hNN₀ hN H hH0 hH
    exact hPoleL N hNN₀ hN H hH0 hH

end
end SlowEquilibration.SphericalPureCapExteriorFixedGeometry
