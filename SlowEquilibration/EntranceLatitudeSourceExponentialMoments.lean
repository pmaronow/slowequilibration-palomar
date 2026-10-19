-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceWeightConstants
public import SlowEquilibration.EntranceLatitudeSourceAxisContinuity
public import SlowEquilibration.SphericalTwoPointCovariance

/-! Genuine latitude exponential moments of the literal source correction.
The sampled H_Q tangent observable, its actual latitude mean and genuine
Gaussian fluctuation moments are used directly. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalLatitudeTensorMoments
open ConditionedEntrance SphericalTwoPointCovariance
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem source_coefficient_nonneg (μ : FiniteMixture) (Q M ζ : ℝ) :
    0≤ sourceLatitudeExponentCoefficient μ Q M ζ := by
  have h := (latitudeExponentialConstant_pos (centerCoefficients (mixtureCoefficients μ) Q)).le
  unfold sourceLatitudeExponentCoefficient
  positivity

private theorem source_moment_coefficient_bounds (μ : FiniteMixture) (Q M ζ : ℝ) :
    sourceLatitudeExponentCoefficient μ Q M ζ≤ sourceLatitudeMomentConstant μ Q M ζ ∧
    sourceLatitudeMomentPrefactor μ Q≤ sourceLatitudeMomentConstant μ Q M ζ ∧
    4*Real.exp (3*latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q))≤
      sourceLatitudeMomentPrefactor μ Q := by
  have he := (Real.exp_pos (latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q))).le
  have he3 := (Real.exp_pos (3*latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q))).le
  have hl := source_coefficient_nonneg μ Q M ζ
  have hp : 0≤ sourceLatitudeMomentPrefactor μ Q := by unfold sourceLatitudeMomentPrefactor;positivity
  refine ⟨?_,?_,?_⟩
  · unfold sourceLatitudeMomentConstant
    linarith
  · unfold sourceLatitudeMomentConstant
    linarith
  · unfold sourceLatitudeMomentPrefactor
    nlinarith [mul_nonneg (sq_nonneg (centerLatitudeMeanConstant μ Q)) he3]

private theorem source_delta_latitude_bound {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) {M : ℝ} (hM : 0≤M)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈regularDisorder)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {e k r : ℝ} (he : |e|≤M) (hk : |k|≤M)
    (hr : |r|≤1) :
    ∀ᵐ u ∂latitudeLaw x (latitudeFrameAt x) r,
      |sourceRegressionCorrection μ Q hQ hnp J u e k x|≤
      sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|) := by
  filter_upwards [latitudeLaw_support hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) hr] with u hu
  have h := actual_sourceRegressionCorrection_abs_le_observable μ hQ hnp hM J hJ u x hu.1 hx he hk
  rw [overlap_comm u x,hu.2] at h
  exact h

/-- Genuine latitude bound for a continuous observable dominated by the actual source envelope. -/
theorem latitude_source_dominated_exp_abs_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ}
    (hr : r∈Ioo (-1 : ℝ) 1) (F : Vector (n+1)→ℝ) (hF : Continuous F)
    (hFb : ∀ᵐ u ∂latitudeLaw x (latitudeFrameAt x) r,
      |F u|≤ sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|)) :
    Integrable (fun u => Real.exp (ζ*|F u|))
      (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,Real.exp (ζ*|F u|) ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeMomentConstant μ Q M ζ*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  let D := sourceLatitudeCorrectionConstant μ Q M
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let K := latitudeExponentialConstant cQ
  let m := latitudeObservableMean cQ J x (latitudeFrameAt x) r
  let a := D*((n+1 : ℕ) : ℝ)*|r|^μ.minDegree
  let b := D*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)
  let t := ζ*b
  let ν := latitudeLaw x (latitudeFrameAt x) r
  have hD : 0≤D := by
    unfold D sourceLatitudeCorrectionConstant
    exact mul_nonneg (regressionOrderConstant_pos μ Q).le
      (by have h := (derivativeConstant_pos cQ).le;unfold sourceLatitudeCenterConstant;dsimp only [cQ] at h;linarith)
  have ht : 0≤t := by dsimp [t,b];positivity
  have hiV := latitudeObservable_exp_abs_integrable hn cQ J hJ.1 x hx (abs_lt.mpr hr).le t
  have hib : Integrable (fun u => Real.exp (ζ*a)*Real.exp (t*|observable cQ J x u|)) ν := hiV.const_mul _
  have hd := hFb
  have hdom : ∀ᵐ u ∂ν,Real.exp (ζ*|F u|)≤
      Real.exp (ζ*a)*Real.exp (t*|observable cQ J x u|) := by
    filter_upwards [hd] with u hu
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hu hζ
    dsimp only [a,t,b,D,cQ]
    nlinarith
  have hif : Integrable (fun u => Real.exp (ζ*|F u|)) ν := by
    apply hib.mono' (((hF).abs.const_mul ζ).rexp.aestronglyMeasurable)
    filter_upwards [hdom] with u hu
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hu
  refine ⟨hif,?_⟩
  apply (integral_mono_ae hif hib hdom).trans
  rw [integral_const_mul]
  have hv := actual_latitude_exp_abs_le hn cQ J hJ.1 x hx (abs_lt.mpr hr).le ht
  have hexp := actual_source_latitude_exponent_le hn μ hQ hM hζ J hJ x hx hr
  have hK := (latitudeExponentialConstant_pos cQ).le
  have hx3 : ζ*a+t*|m|+K*(1+t^2)≤3*K+sourceLatitudeExponentCoefficient μ Q M ζ*sourceLatitudeWeightPower n μ r := by
    have hbase : ζ*a+t*|m|+3*K*(1+t^2)≤3*K+
        sourceLatitudeExponentCoefficient μ Q M ζ*sourceLatitudeWeightPower n μ r := by
      convert hexp using 1
      ring
    nlinarith [mul_nonneg hK (sq_nonneg t)]
  have hs := source_moment_coefficient_bounds μ Q M ζ
  have hp : 0≤ sourceLatitudeWeightPower n μ r := by unfold sourceLatitudeWeightPower;positivity
  have hE : 4*Real.exp (ζ*a+t*|m|+K*(1+t^2))≤
      sourceLatitudeMomentPrefactor μ Q*Real.exp
        (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx3) (by norm_num : (0 : ℝ)≤4)).trans
    rw [Real.exp_add]
    have hh := mul_le_mul hs.2.2 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.1 hp))
      (Real.exp_pos _).le (by unfold sourceLatitudeMomentPrefactor;positivity)
    convert hh using 1
    ring
  have hVbound : Real.exp (ζ*a)*(∫ u,Real.exp (t*|observable cQ J x u|) ∂ν)≤
      4*Real.exp (ζ*a+t*|m|+K*(1+t^2)) := by
    apply (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans_eq
    rw [mul_left_comm,←Real.exp_add]
    dsimp only [m,K]
    congr 1
    ring
  apply (hVbound.trans hE).trans
  exact mul_le_mul_of_nonneg_right hs.2.1 (Real.exp_pos _).le




/-- Genuine latitude bound for a continuous observable dominated by the actual source envelope. -/
theorem latitude_source_dominated_observable_square_exp_abs_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ}
    (hr : r∈Ioo (-1 : ℝ) 1) (F : Vector (n+1)→ℝ) (hF : Continuous F)
    (hFb : ∀ᵐ u ∂latitudeLaw x (latitudeFrameAt x) r,
      |F u|≤ sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|)) :
    let cQ := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (fun u => (observable cQ J x u)^2*Real.exp (ζ*|F u|))
      (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,(observable cQ J x u)^2*Real.exp (ζ*|F u|)
      ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeMomentConstant μ Q M ζ*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2))*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  dsimp only
  let D := sourceLatitudeCorrectionConstant μ Q M
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let K := latitudeExponentialConstant cQ
  let m := latitudeObservableMean cQ J x (latitudeFrameAt x) r
  let a := D*((n+1 : ℕ) : ℝ)*|r|^μ.minDegree
  let b := D*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)
  let t := ζ*b
  let ν := latitudeLaw x (latitudeFrameAt x) r
  have hD : 0≤D := by
    unfold D sourceLatitudeCorrectionConstant
    exact mul_nonneg (regressionOrderConstant_pos μ Q).le
      (by have h := (derivativeConstant_pos cQ).le;unfold sourceLatitudeCenterConstant;dsimp only [cQ] at h;linarith)
  have ht : 0≤t := by dsimp [t,b];positivity
  have hV := actual_latitude_second_exp_abs_le hn cQ J hJ.1 x hx (abs_lt.mpr hr).le ht
  have hib : Integrable (fun u => Real.exp (ζ*a)*((observable cQ J x u)^2*Real.exp (t*|observable cQ J x u|))) ν :=
    hV.1.const_mul _
  have hd := hFb
  have hdom : ∀ᵐ u ∂ν,(observable cQ J x u)^2*Real.exp (ζ*|F u|)≤
      Real.exp (ζ*a)*((observable cQ J x u)^2*Real.exp (t*|observable cQ J x u|)) := by
    filter_upwards [hd] with u hu
    have hex : Real.exp (ζ*|F u|)≤
        Real.exp (ζ*a)*Real.exp (t*|observable cQ J x u|) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hu hζ
      dsimp only [a,t,b,D,cQ]
      nlinarith
    apply (mul_le_mul_of_nonneg_left hex (sq_nonneg (observable cQ J x u))).trans_eq
    ring
  have hif : Integrable (fun u => (observable cQ J x u)^2*Real.exp (ζ*|F u|)) ν := by
    apply hib.mono' (((observable_continuous cQ J x).pow 2).mul
      (((hF).abs.const_mul ζ).rexp) |>.aestronglyMeasurable)
    filter_upwards [hdom] with u hu
    change ‖(observable cQ J x u)^2*Real.exp (ζ*|F u|)‖≤_
    simpa only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)] using hu
  refine ⟨hif,?_⟩
  apply (integral_mono_ae hif hib hdom).trans
  rw [integral_const_mul]
  have hexp := actual_source_latitude_exponent_le hn μ hQ hM hζ J hJ x hx hr
  have hx3 : ζ*a+t*|m|+3*K*(1+t^2)≤3*K+
      sourceLatitudeExponentCoefficient μ Q M ζ*sourceLatitudeWeightPower n μ r := by
    convert hexp using 1
    ring
  have hmean := actual_center_latitude_mean_square_le hn μ hQ J hJ x hx hr
  have hVbound : Real.exp (ζ*a)*(∫ u,(observable cQ J x u)^2*Real.exp (t*|observable cQ J x u|) ∂ν)≤
      24*(1+m^2)*Real.exp (ζ*a+t*|m|+3*K*(1+t^2)) := by
    apply (mul_le_mul_of_nonneg_left hV.2 (Real.exp_pos _).le).trans_eq
    rw [mul_left_comm,←Real.exp_add]
    dsimp only [m,K]
    congr 1
    ring
  apply hVbound.trans
  have hpre : 24*(1+m^2)*Real.exp (ζ*a+t*|m|+3*K*(1+t^2))≤
      sourceLatitudeMomentPrefactor μ Q*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2))*
        Real.exp (sourceLatitudeExponentCoefficient μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ)≤24))
      (Real.exp_le_exp.mpr hx3) (Real.exp_pos _).le (by positivity)
    apply hh.trans_eq
    rw [Real.exp_add]
    dsimp only [sourceLatitudeMomentPrefactor]
    ring
  apply hpre.trans
  have hs := source_moment_coefficient_bounds μ Q M ζ
  have hp : 0≤ sourceLatitudeWeightPower n μ r := by unfold sourceLatitudeWeightPower;positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right hs.2.1 (by positivity))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.1 hp)) (Real.exp_pos _).le
    (by have h := (sourceLatitudeMomentConstant_pos μ Q M ζ).le;positivity)


/-- Literal source correction has a true latitude exponential moment
bounded by the fixed actual-model radial exponent, with honest integrability. -/
theorem actual_sourceRegressionCorrection_latitude_exp_abs_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {e k r : ℝ} (he : |e|≤M) (hk : |k|≤M)
    (hr : r∈Ioo (-1 : ℝ) 1) :
    Integrable (fun u => Real.exp (ζ*|sourceRegressionCorrection μ Q hQ hnp J u e k x|))
      (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,Real.exp (ζ*|sourceRegressionCorrection μ Q hQ hnp J u e k x|) ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeMomentConstant μ Q M ζ*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  exact latitude_source_dominated_exp_abs_le hn μ hQ.le hM hζ J hJ x hx hr
    (fun u => sourceRegressionCorrection μ Q hQ hnp J u e k x)
    (sourceRegressionCorrection_axis_continuous μ hQ hnp J e k x)
    (source_delta_latitude_bound hn μ hQ hnp hM J hJ.1 x hx he hk (abs_lt.mpr hr).le)


/-- Literal source correction times its sampled H_Q tangent square has
its genuine latitude bound, with the exact radial second-moment order. -/
theorem actual_sourceRegressionCorrection_latitude_observable_square_exp_abs_le {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ) (J : Disorder (n+1) μ.maxDegree)
    (hJ : J∈originalLatitudeMeanGood n μ) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    {e k r : ℝ} (he : |e|≤M) (hk : |k|≤M) (hr : r∈Ioo (-1 : ℝ) 1) :
    let cQ := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (fun u => (observable cQ J x u)^2*Real.exp (ζ*|sourceRegressionCorrection μ Q hQ hnp J u e k x|))
      (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,(observable cQ J x u)^2*Real.exp (ζ*|sourceRegressionCorrection μ Q hQ hnp J u e k x|)
      ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeMomentConstant μ Q M ζ*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2))*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  exact latitude_source_dominated_observable_square_exp_abs_le hn μ hQ.le hM hζ J hJ x hx hr
    (fun u => sourceRegressionCorrection μ Q hQ hnp J u e k x)
    (sourceRegressionCorrection_axis_continuous μ hQ hnp J e k x)
    (source_delta_latitude_bound hn μ hQ hnp hM J hJ.1 x hx he hk (abs_lt.mpr hr).le)

end
end SlowEquilibration.EntranceLatitudeTangentObservable
