-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralRSPressure
public import SlowEquilibration.SphericalTaylorCoreLower
public import SlowEquilibration.SphericalResidualTemperatureConcentration

@[expose] public section

/-! # Genuine canonical thermal core for every finite mixture

The general finite RS theorem applies directly to the actual nonnegative
Taylor residual. Its proved auxiliary static certificate then supplies the
physical corrected-temperature mean and tail estimates. The exact posterior
law, marked critical counts and two coarea integrations give the literal
planted core bound, including quadratic mixtures of arbitrary parity.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Classical Metric
open scoped ENNReal Topology BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SlowEquilibration.FiniteMixture
open SphericalModel

theorem general_qStar_taylorResidual_pressure_per_ambient_tendsto
    (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => ((N : ℝ)/((N+j : ℕ) : ℝ))*
      quenchedPressure N ν (dimensionCorrectedTemperature β j N)) atTop
      (𝓝 ((β^2*(μ.xi 1-μ.xi q)-q)/2)) := by
  let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
    (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
  have hp := quenchedPressure_tendsto_dimensionCorrected_per_ambient ν
    (μ.dynamicalThreshold_pos.trans hβ).le j
    (general_quenchedPressure_tendsto_annealed_le_static ν
      (μ.dynamicalThreshold_pos.trans hβ).le
      (CSTaylorResidualCertificate.qStar_taylorResidual_le_staticThreshold μ hβ))
  dsimp only [ν] at hp ⊢
  rw [μ.qStar_taylorResidual_annealed_value hβ] at hp
  exact hp

theorem general_qStar_taylorResidual_corrected_logPartition_lower_tail
    (μ : FiniteMixture)
    {β ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) (hε : 0 < ε) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    let F := (β^2*(μ.xi 1-μ.xi q)-q)/2
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      disorderLaw N ν.maxDegree {J | Real.log
        (mixturePartition ν (dimensionCorrectedTemperature β j N) J)/((N+j : ℕ) : ℝ)
          < F-ε} ≤ ENNReal.ofReal (2*Real.exp (-c*((N+j : ℕ) : ℝ))) := by
  exact dimensionCorrected_logPartition_lower_tail_of_pressure_limit _
    (μ.dynamicalThreshold_pos.trans hβ) j hε
    (μ.general_qStar_taylorResidual_pressure_per_ambient_tendsto hβ j)



end SlowEquilibration.FiniteMixture

namespace SlowEquilibration.SphericalTaylorRemainder.GeneralFinite
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.StrongFieldComplexity
open SlowEquilibration.SphericalMarkedWindows SlowEquilibration.SphericalForm
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphericalSequentialRegression

theorem qStar_posterior_transverse_pressure_lower_tail (μ : FiniteMixture)
    {β ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+2)),‖w‖^2=((n+2 : ℕ) : ℝ) →
      ∀ (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)),(∀ z,inner ℝ (e z) w=0) →
      ∀ q : ℝ,|q|≤1 → ∀ (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
      (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))),
      coefficientKernel (latitudeJointCLM c w e q y hy) target
        {J | transverseRemainderPressure c w e q Q β J y<F-ε}≤
      ENNReal.ofReal (2*Real.exp (-γ*((n+2 : ℕ) : ℝ))) := by
  dsimp only
  obtain ⟨γ,hγ,hbound⟩ := μ.general_qStar_taylorResidual_corrected_logPartition_lower_tail hβ 2 hε
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with n hn hdim
  intro w hw e he q hq y hy target
  rw [latitude_posterior_residual_sublevel_measure_eq hdim μ (μ.qStar_solves_plateau hβ).1 β _ w hw e he hq y hy target]
  exact hn



theorem qStar_posterior_transverse_pressure_exponential (μ : FiniteMixture)
    {β ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+2)),‖w‖^2=((n+2 : ℕ) : ℝ) →
      ∀ (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)),(∀ z,inner ℝ (e z) w=0) →
      ∀ q : ℝ,|q|≤1 → ∀ (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
      (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))),
      coefficientKernel (latitudeJointCLM c w e q y hy) target
        {J | transverseRemainderPressure c w e q Q β J y<F-ε}≤
      ENNReal.ofReal (Real.exp (-γ*((n+2 : ℕ) : ℝ))) := by
  dsimp only
  have hbound := qStar_posterior_transverse_pressure_lower_tail μ hβ hε
  obtain ⟨γ,hγ,hbound⟩ := hbound
  have hdim : ∀ᶠ n : ℕ in atTop,
      StrongFieldComplexity.polynomialAbsorptionThreshold 2 0 (γ/2)≤((n+2 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (StrongFieldComplexity.polynomialAbsorptionThreshold 2 0 (γ/2)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (StrongFieldComplexity.polynomialAbsorptionThreshold 2 0 (γ/2))≤n+2 by omega))
  refine ⟨γ/2,by positivity,?_⟩
  filter_upwards [hbound,hdim] with n hn hdim
  intro w hw e he q hq y hy target
  apply (hn w hw e he q hq y hy target).trans
  apply ENNReal.ofReal_le_ofReal
  have hp := StrongFieldComplexity.polynomial_le_exp_of_threshold 0 (by norm_num : (0 : ℝ)≤2)
    (show 0<γ/2 by positivity) hdim
  simp only [pow_zero,mul_one] at hp
  calc
    _ ≤ Real.exp ((γ/2)*((n+2 : ℕ) : ℝ))*Real.exp (-γ*((n+2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem qStar_actual_bad_thermal_critical_count (μ : FiniteMixture)
   
    {β ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (hab : latitudeCurvatureVariance
        (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q)
    (L U K Z : ℝ) {g : ℝ} (hg : 0<g)
    (hK : 2*Real.sqrt (latitudeCurvatureVariance
      (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q)+g≤K) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    let S := rectangularScoreWindow (Icc L U) (Icc K Z)
    ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ z,inner ℝ (e z) w=0) →
      (∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => if actualLatitudeScore c w e q J y∈S ∧
          transverseRemainderPressure c w e q Q β J y<F-ε then 1 else 0) J
            ∂disorderLaw (n+3) μ.maxDegree)≤ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
  obtain ⟨γ,hγ,hpost⟩ := qStar_posterior_transverse_pressure_exponential μ hβ hε
  have hcount := latitude_actual_bad_count_eventually_exponential μ
    (μ.qStar_solves_plateau hβ).1.1 hq0 hq1 hab L U K Z hg hγ hK
  refine ⟨γ/4,by positivity,?_⟩
  filter_upwards [hcount,(tendsto_add_atTop_nat 1).eventually hpost] with n hn hp
  intro w hw e he
  let E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)) :=
    {p | transverseRemainderPressure c w e q Q β p.1 p.2<F-ε}
  have hE : MeasurableSet E := measurableSet_transverseRemainder_bad c w e q Q β (F-ε)
  apply hn w hw e he E hE
  intro y hy z _
  have hh := hp w hw e he q hq1.le y hy (jointScoreTarget (n+1) (((n+3 : ℕ) : ℝ) • z))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht
  exact ht

theorem qStar_bad_thermal_critical_probability (μ : FiniteMixture)
   
    {β ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (hab : latitudeCurvatureVariance
        (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q)
    (L U K Z : ℝ) {g : ℝ} (hg : 0<g)
    (hK : 2*Real.sqrt (latitudeCurvatureVariance
      (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q)+g≤K) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    let S := rectangularScoreWindow (Icc L U) (Icc K Z)
    ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ z,inner ℝ (e z) w=0) →
      disorderLaw (n+3) μ.maxDegree
        {J | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
          surfaceGradient (latitudeField c J w e q) y=0 ∧
          actualLatitudeScore c w e q J y∈S ∧
          transverseRemainderPressure c w e q Q β J y<F-ε}≤
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
  let S := rectangularScoreWindow (Icc L U) (Icc K Z)
  have hQ : 0<Q := (μ.qStar_solves_plateau hβ).1.1
  have hc : ∀ p,0≤c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0<firstCovariance c 1 := by
    dsimp only [c]
    rw [firstCovariance_center,firstCovariance_mixture]
    exact mul_pos hQ (μ.xi1_pos hQ)
  obtain ⟨η,hη,hcount⟩ := qStar_actual_bad_thermal_critical_count μ hβ hε hq0 hq1 hab L U K Z hg hK
  refine ⟨η,hη,?_⟩
  filter_upwards [hcount] with n hn
  intro w hw e he
  let E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)) :=
    {p | actualLatitudeScore c w e q p.1 p.2∈S ∧
      transverseRemainderPressure c w e q Q β p.1 p.2<F-ε}
  have hS : MeasurableSet S := rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Icc
  have hscore : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) =>
      actualLatitudeScore c w e q p.1 p.2) :=
    (latitudeScore_jointContinuous c w e q).measurable.const_smul (((n+3 : ℕ) : ℝ)⁻¹)
  have hE : MeasurableSet E := (hS.preimage hscore).inter
    (measurableSet_transverseRemainder_bad c w e q Q β (F-ε))
  let psi : Disorder (n+3) μ.maxDegree → Vector (n+2) → ℝ≥0∞ :=
    fun J y => if actualLatitudeScore c w e q J y∈S ∧
      transverseRemainderPressure c w e q Q β J y<F-ε then 1 else 0
  let C := actualLatitudeSphereCount c w e q psi
  have hpsi : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) => psi p.1 p.2) :=
    Measurable.ite hE measurable_const measurable_const
  have hC : AEMeasurable C (disorderLaw (n+3) μ.maxDegree) :=
    (actual_latitude_sphere_marked_kacRice (by omega) c hc hfirst w hw e he hq1 psi hpsi).1
  have hsub : {J : Disorder (n+3) μ.maxDegree | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0 ∧
      actualLatitudeScore c w e q J y∈S ∧ transverseRemainderPressure c w e q Q β J y<F-ε}⊆
      {J | 1≤C J} := by
    rintro J ⟨y,hy,hcrit,hscorey,hbad⟩
    have ht := ENNReal.le_tsum (f := fun z : {z : Vector (n+2) | ‖z‖^2=((n+2 : ℕ) : ℝ) ∧
        surfaceGradient (latitudeField c J w e q) z=0} => psi J z) ⟨y,hy,hcrit⟩
    have hvalue : psi J y=1 := ite_eq_left ⟨hscorey,hbad⟩
    rw [hvalue] at ht
    exact ht
  have hm : disorderLaw (n+3) μ.maxDegree {J | 1≤C J}≤∫⁻ J,C J ∂disorderLaw (n+3) μ.maxDegree := by
    simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1
  exact ((measure_mono hsub).trans hm).trans (hn w hw e he)



theorem qStar_good_thermal_critical_point (μ : FiniteMixture)
   
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
  obtain ⟨τ,hτ,hbad⟩ := qStar_bad_thermal_critical_probability μ hβ hε₂ hq0 hq1 hab
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

theorem qStar_good_planted_transverse_band (μ : FiniteMixture)
   
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
  obtain ⟨α,hα,hgood⟩ := qStar_good_thermal_critical_point μ hβ
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

theorem qStar_shifted_core_partition_lower_tail (μ : FiniteMixture)
   
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      disorderLaw (n+3) μ.maxDegree
        {J | partitionOn β (fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β w))
          (coreBand w Q δ)<Real.exp (((n+3 : ℕ) : ℝ)*(plantedProfileTrial μ β Q-ε))}≤
        6*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  have hQ : Q∈Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  obtain ⟨q,hq,hclose,η,hη,hgood⟩ := qStar_good_planted_transverse_band μ hβ hδ (half_pos hε)
  have hqpos : 0<q := (Real.sqrt_pos.mpr hQ.1).trans hq.1
  have hqabs : |q|<1 := by rw [abs_of_pos hqpos]; exact hq.2
  obtain ⟨K,hK,hgrad⟩ := exists_planted_regularDisorder_gradient_bound μ β
  let A := Ioo (Q-δ) (Q+δ)
  have hrA : bandOuterLatitude Q q∈A := by
    have hh := abs_lt.mp hclose
    exact ⟨by linarith,by linarith⟩
  have hthick := transverseBand_partitionOn_eventually_lower_of_gradient_bound
    (β := β) hQ hqabs hK.le (half_pos hε) isOpen_Ioo hrA
  refine ⟨η,hη,?_⟩
  filter_upwards [hgood,(tendsto_add_atTop_nat 1).eventually hthick] with n hn hthick
  intro w hw
  let e := latitudeFrameAt w
  have he : ∀ z,inner ℝ (e z) w=0 := latitudeFrameAt_orthogonal w hw
  apply (measure_mono ?_).trans (hn w hw e he)
  intro J hJ hg
  obtain ⟨hreg,y,hy,hband⟩ := hg
  let H := fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β w)
  have hH : Differentiable ℝ H :=
    (field_contDiff (mixtureCoefficients μ) _).differentiable (by simp)
  have hgH : ∀ x∈closedBall 0 (Real.sqrt ((n+3 : ℕ) : ℝ)),‖fderiv ℝ H x‖≤K*Real.sqrt ((n+3 : ℕ) : ℝ) := by
    intro x hx
    exact hgrad (n+3) (by omega) w hw J hreg x
      (by simpa only [mem_closedBall,dist_zero_right] using hx)
  let B := plantedProfileTrial μ β Q-ε/2-Real.log (1-Q)/2
  have hB : B≤transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y := by
    dsimp only [B]
    linarith
  have hz := hthick H hH hgH w hw y hy B hB
  have hexp : B+Real.log (1-Q)/2-ε/2=plantedProfileTrial μ β Q-ε := by dsimp only [B]; ring
  rw [hexp] at hz
  have hsub : overlapRegion w A⊆coreBand w Q δ := by
    intro x hx
    change overlap x w∈Ioo (Q-δ) (Q+δ) at hx
    change |overlap x w-Q|≤δ
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  exact (not_lt_of_ge (hz.trans (partitionOn_mono (by omega) β H hH.continuous hsub))) hJ

theorem qStar_planted_core_partition_lower_tail (μ : FiniteMixture)
   
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      plantedLaw (N := n+3) (mixtureCoefficients μ) β (coreLowerBadEvent (n+3) μ β δ ε)≤
        ENNReal.ofReal (Real.exp (-γ*((n+3 : ℕ) : ℝ))) := by
  obtain ⟨η,hη,hbound⟩ := qStar_shifted_core_partition_lower_tail μ hβ hδ hε
  have hdim : ∀ᶠ n : ℕ in atTop,polynomialAbsorptionThreshold 6 0 (η/2)≤((n+3 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (polynomialAbsorptionThreshold 6 0 (η/2)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast
      (show Nat.ceil (polynomialAbsorptionThreshold 6 0 (η/2))≤n+3 by omega))
  refine ⟨η/2,by positivity,?_⟩
  filter_upwards [hbound,hdim] with n hn hdim
  apply planted_measure_le_of_uniform_shift_probability (by omega) (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β (coreLowerBadEvent_measurable _ μ β δ ε) (Real.exp_pos _).le
  intro w hw
  apply (hn w hw).trans
  have hp := polynomial_le_exp_of_threshold 0 (by norm_num : (0 : ℝ)≤6) (half_pos hη) hdim
  simp only [pow_zero,mul_one] at hp
  calc
    _ = ENNReal.ofReal (6*Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ ENNReal.ofReal (Real.exp ((η/2)*((n+3 : ℕ) : ℝ))*Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 2; ring




theorem qStar_planted_core_partition_lower_tail_allDimensions (μ : FiniteMixture)
   
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ N : ℕ in atTop,
      plantedLaw (N := N) (mixtureCoefficients μ) β (coreLowerBadEvent N μ β δ ε)≤
        ENNReal.ofReal (Real.exp (-γ*(N : ℝ))) := by
  obtain ⟨γ,hγ,hbound⟩ := qStar_planted_core_partition_lower_tail μ hβ hδ hε
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hbound
  refine ⟨γ,hγ,eventually_atTop.2 ⟨n₀+3,?_⟩⟩
  intro N hN
  obtain ⟨m,rfl⟩ : ∃ m : ℕ,N=m+3 := ⟨N-3,by omega⟩
  exact hn₀ m (by omega)

end SlowEquilibration.SphericalTaylorRemainder.GeneralFinite
