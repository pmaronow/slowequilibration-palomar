-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorBadCriticalProbability
public import SlowEquilibration.SphericalLatitudeCriticalLocalization

@[expose] public section

/-! A high actual critical point with a good thermal transverse field,
selected from the same tensor disorder with exponential failure probability. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.SphericalForm SlowEquilibration.StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem qStar_good_thermal_critical_point (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree)
    {β ε₁ ε₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hε₁ : 0<ε₁) (hε₂ : 0<ε₂) {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (hab : latitudeCurvatureVariance
        (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ z,inner ℝ (e z) w=0) →
      disorderLaw (n+3) μ.maxDegree {J | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
        surfaceGradient (latitudeField c J w e q) y=0 ∧
        Real.sqrt a-ε₁<actualLatitudeScore c w e q J y 0 ∧
        F-ε₂≤transverseRemainderPressure c w e q Q β J y}≤
          5*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
  let U := derivativeConstant c
  let k := radialEndpoint a b
  let s := min ε₁ (Real.sqrt a/2)
  have hQ : 0<Q := (μ.qStar_solves_plateau hβ).1.1
  have ha : 0<a := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hb : 0<b := center_latitudeCurvatureVariance_pos μ hQ hq1
  have hs : 0<s := lt_min hε₁ (by positivity)
  have hsmall : s<Real.sqrt a := (min_le_right _ _).trans_lt (by nlinarith [Real.sqrt_pos.mpr ha])
  have hedge : 2*Real.sqrt b<k := radialEndpoint_gt_edge hb hab
  let δ := (k-2*Real.sqrt b)/4
  have hδ : 0<δ := by dsimp only [δ]; linarith
  have hK : 2*Real.sqrt b+δ≤k-δ := by dsimp only [δ]; linarith
  obtain ⟨α,hα,hmax⟩ := latitude_high_critical_localization μ hQ hq0 hq1 hab hs hδ hsmall
  obtain ⟨τ,hτ,hbad⟩ := qStar_bad_thermal_critical_probability μ hscope hβ hε₂ hq0 hq1 hab
    (Real.sqrt a-s) U (k-δ) (k+δ) hδ hK
  let η := min α τ
  have hη : 0<η := lt_min hα hτ
  refine ⟨η,hη,?_⟩
  filter_upwards [hmax,hbad] with n hnmax hnbad
  intro w hw e he
  let Low : Set (Disorder (n+3) μ.maxDegree) := {J | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    surfaceGradient (latitudeField c J w e q) y=0 ∧
    Real.sqrt a-s<actualLatitudeScore c w e q J y 0 ∧
    actualLatitudeScore c w e q J y 0≤U ∧ |actualLatitudeScore c w e q J y 1-k|<δ}
  let Bad : Set (Disorder (n+3) μ.maxDegree) := {J | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    surfaceGradient (latitudeField c J w e q) y=0 ∧
    actualLatitudeScore c w e q J y∈rectangularScoreWindow (Icc (Real.sqrt a-s) U) (Icc (k-δ) (k+δ)) ∧
    transverseRemainderPressure c w e q Q β J y<F-ε₂}
  have hsub : {J : Disorder (n+3) μ.maxDegree | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0 ∧
      Real.sqrt a-ε₁<actualLatitudeScore c w e q J y 0 ∧
      F-ε₂≤transverseRemainderPressure c w e q Q β J y}⊆Low∪Bad := by
    intro J hJ
    by_cases hlow : J∈Low
    · exact Or.inl hlow
    right
    obtain ⟨y,hy,hcrit,hheight,hupper,hrad⟩ := not_not.mp hlow
    have hthermal : transverseRemainderPressure c w e q Q β J y<F-ε₂ := by
      by_contra hh
      apply hJ
      exact ⟨y,hy,hcrit,(sub_le_sub_left (min_le_left ε₁ (Real.sqrt a/2)) _).trans_lt hheight,not_lt.mp hh⟩
    have hr := abs_lt.mp hrad
    exact ⟨y,hy,hcrit,⟨⟨hheight.le,hupper⟩,⟨by linarith,by linarith⟩⟩,hthermal⟩
  have hN : (0 : ℝ)≤((n+3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrate (r : ℝ) (hr : η≤r) : ENNReal.ofReal (Real.exp (-r*((n+3 : ℕ) : ℝ)))≤
      ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hr hN]
  apply ((measure_mono hsub).trans (measure_union_le Low Bad)).trans
  calc
    _ ≤ 4*ENNReal.ofReal (Real.exp (-α*((n+3 : ℕ) : ℝ)))+
        ENNReal.ofReal (Real.exp (-τ*((n+3 : ℕ) : ℝ))) :=
      add_le_add (hnmax w hw e he) (hnbad w hw e he)
    _ ≤ 4*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ)))+
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
      apply add_le_add
      · simpa only [mul_comm] using mul_le_mul_left (hrate α (min_le_left _ _)) 4
      · exact hrate τ (min_le_right _ _)
    _ = _ := by ring

end
end SlowEquilibration.SphericalTaylorRemainder
