-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeScoreBounds
public import SlowEquilibration.SphericalLatitudeRadialCountDecay
public import SlowEquilibration.SphericalLatitudeStrongFieldMaximum
public import SlowEquilibration.SphericalLatitudeBadCriticalProbability

@[expose] public section

/-! # Actual high latitude critical points have the sharp radial score -/
namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalMarkedWindows
open SphericalForm StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_offEndpoint_critical_probability (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    (H : ℝ) {Z δ : ℝ} (hZ : 0 ≤ Z) (hδ : 0 < δ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let b := latitudeCurvatureVariance c q
    ∃ η : ℝ,0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ x,inner ℝ (e x) w=0) →
      disorderLaw (n+3) μ.maxDegree {J | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
        surfaceGradient (latitudeField c J w e q) y=0 ∧
        actualLatitudeScore c w e q J y ∈
          rectangularScoreWindow (Icc 0 H) (radialExcludedWindow a b Z δ)} ≤
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  obtain ⟨η,hη,hcount⟩ := latitude_offEndpoint_count_exponential μ hQ hq0 hq1 hab H hZ hδ
  refine ⟨η,hη,?_⟩
  filter_upwards [hcount] with n hn
  intro w hw e he
  let S := rectangularScoreWindow (Icc 0 H) (radialExcludedWindow a b Z δ)
  let E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)) :=
    {p | actualLatitudeScore c w e q p.1 p.2 ∈ S}
  have hscore : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) =>
      actualLatitudeScore c w e q p.1 p.2) :=
    (latitudeScore_jointContinuous c w e q).measurable.const_smul (((n+3 : ℕ) : ℝ)⁻¹)
  have hS : MeasurableSet S := rectangularScoreWindow_measurable _ _ measurableSet_Icc
    (radialExcludedWindow_measurable a b Z δ)
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0 < firstCovariance c 1 := by
    rw [firstCovariance_center,firstCovariance_mixture]
    exact mul_pos hQ (mixture_xi1_pos μ hQ)
  have hp := latitude_bad_critical_probability_le_count (by omega) c hc hfirst w hw e he hq1
    E (hS.preimage hscore)
  exact hp.trans (hn w hw e he)

/-- The actual sharp high critical point lies in a fixed compact height
window and any prescribed open neighborhood of the positive radial endpoint.
Constants and dimension threshold precede every reference axis/frame. -/
theorem latitude_high_critical_localization (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsmall : ε < Real.sqrt (latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let b := latitudeCurvatureVariance c q
    ∃ η : ℝ,0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ x,inner ℝ (e x) w=0) →
      disorderLaw (n+3) μ.maxDegree {J | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
        surfaceGradient (latitudeField c J w e q) y=0 ∧
        Real.sqrt a-ε < actualLatitudeScore c w e q J y 0 ∧
        actualLatitudeScore c w e q J y 0 ≤ derivativeConstant c ∧
        |actualLatitudeScore c w e q J y 1-radialEndpoint a b| < δ} ≤
          4*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let C := derivativeConstant c
  have hC : 0 < C := derivativeConstant_pos c
  obtain ⟨α,hα,hmax⟩ := latitude_strongField_maximum_lower μ hQ hq0 hq1 hab hε
  obtain ⟨τ,hτ,hoff⟩ := latitude_offEndpoint_critical_probability μ hQ hq0 hq1 hab C hC.le hδ
  let η := min 1 (min α τ)
  have hη : 0 < η := lt_min (by norm_num) (lt_min hα hτ)
  refine ⟨η,hη,?_⟩
  filter_upwards [hmax,hoff] with n hnmax hnoff
  intro w hw e he
  let Low : Set (Disorder (n+3) μ.maxDegree) := {J | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    ((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε)<latitudeField c J w e q y}
  let Bad : Set (Disorder (n+3) μ.maxDegree) := {J | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    surfaceGradient (latitudeField c J w e q) y=0 ∧ actualLatitudeScore c w e q J y ∈
      rectangularScoreWindow (Icc 0 C) (radialExcludedWindow a b C δ)}
  have hsub : {J | ¬∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0 ∧
      Real.sqrt a-ε < actualLatitudeScore c w e q J y 0 ∧
      actualLatitudeScore c w e q J y 0 ≤ C ∧
      |actualLatitudeScore c w e q J y 1-radialEndpoint a b| < δ} ⊆
      (regularDisorder (N := n+3) (P := μ.maxDegree))ᶜ ∪ (Low ∪ Bad) := by
    intro J hJ
    by_cases hreg : J ∈ regularDisorder
    · right
      by_cases hlow : J ∈ Low
      · exact Or.inl hlow
      right
      have hx : ∃ x,‖x‖^2=((n+2 : ℕ) : ℝ) ∧
          ((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε)<latitudeField c J w e q x := not_not.mp hlow
      obtain ⟨x,hx,hhigh⟩ := hx
      obtain ⟨y,hy,hcrit,hm⟩ := exists_sphere_maximum_critical (latitudeField c J w e q)
        ((latitudeField_contDiff c J w e q).of_le (by simp))
      have hv := latitudeScore_regularDisorder_bounds c J hreg w hw e he hq1.le y hy
      have hN : (0:ℝ) < ((n+3 : ℕ) : ℝ) := by positivity
      have hh : Real.sqrt a-ε < actualLatitudeScore c w e q J y 0 := by
        rw [actualLatitudeScore_zero]
        apply (lt_div_iff₀ hN).mpr
        simpa only [mul_comm] using hhigh.trans_le (hm x hx)
      have h0 : 0 ≤ actualLatitudeScore c w e q J y 0 := by linarith
      have hupper : actualLatitudeScore c w e q J y 0 ≤ C := (le_abs_self _).trans hv.1
      have hrad : δ ≤ |actualLatitudeScore c w e q J y 1-radialEndpoint a b| := by
        by_contra hn
        exact hJ ⟨y,hy,hcrit,hh,hupper,not_le.mp hn⟩
      exact ⟨y,hy,hcrit,⟨⟨h0,hupper⟩,⟨abs_le.mp hv.2,hrad⟩⟩⟩
    · exact Or.inl hreg
  have hN : (0:ℝ) ≤ ((n+3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrate (r : ℝ) (hr : η ≤ r) :
      ENNReal.ofReal (Real.exp (-r*((n+3 : ℕ) : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hr hN]
  have hreg := (regularDisorder_failure_ennreal (N := n+3) (P := μ.maxDegree) (by omega)).trans
    (by simpa only [neg_mul,one_mul] using hrate 1 (min_le_left _ _))
  have hlow := (hnmax w hw e he).trans
    (by simpa only [mul_comm] using
      mul_le_mul_left (hrate α ((min_le_right _ _).trans (min_le_left _ _))) 2)
  have hbad := (hnoff w hw e he).trans
    (hrate τ ((min_le_right _ _).trans (min_le_right _ _)))
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add le_rfl (measure_union_le Low Bad)).trans
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ)))+
        (2*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ)))+
          ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ)))) :=
      by simpa only [neg_mul,mul_neg,mul_comm,Low,Bad,c,a,b] using
        add_le_add hreg (add_le_add hlow hbad)
    _ = _ := by ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
