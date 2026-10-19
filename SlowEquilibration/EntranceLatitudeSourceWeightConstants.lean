-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeUncenteredMoments
public import SlowEquilibration.EntranceLatitudeSourceCorrectionBound

/-! Actual-model constants and literal latitude exponent arithmetic for
source8.2. The coefficients are fixed from the mixture,Q,mark bound and
exponential parameter before dimension is selected. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open SphericalModel SphericalForm SphericalGaussianJet SphericalLatitudeTensorMoments
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem correction_constant_nonneg (p : ℕ) : 0≤latitudeCorrectionUniformConstant p := by
  unfold latitudeCorrectionUniformConstant
  apply Finset.sum_nonneg
  intro S hS
  apply List.sum_nonneg
  intro a ha
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp ha
  positivity

theorem centerLatitudeMeanConstant_pos (μ : FiniteMixture) (Q : ℝ) : 0<centerLatitudeMeanConstant μ Q := by
  have hl : 0≤centerLatitudeLeadingConstant μ Q := by
    unfold centerLatitudeLeadingConstant
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) (blockThreshold_pos p).le)
  have hc : 0≤centerLatitudeCorrectionConstant μ Q := by
    unfold centerLatitudeCorrectionConstant
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (Real.sqrt_nonneg _) (correction_constant_nonneg _))
  unfold centerLatitudeMeanConstant
  linarith

def sourceLatitudeExponentCoefficient (μ : FiniteMixture) (Q M ζ : ℝ) : ℝ :=
  let D := sourceLatitudeCorrectionConstant μ Q M
  let A := centerLatitudeMeanConstant μ Q
  let K := latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q)
  1+|ζ*D|+|ζ*D*A|+3*K*(ζ*D)^2

def sourceLatitudeMomentPrefactor (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  24*(1+2*(centerLatitudeMeanConstant μ Q)^2)*
    Real.exp (3*latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q))

def sourceLatitudeMomentConstant (μ : FiniteMixture) (Q M ζ : ℝ) : ℝ :=
  1+4*Real.exp (latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q))+
    sourceLatitudeMomentPrefactor μ Q+sourceLatitudeExponentCoefficient μ Q M ζ

def sourceLatitudeWeightPower (n : ℕ) (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2)+
    Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)

theorem sourceLatitudeMomentConstant_pos (μ : FiniteMixture) (Q M ζ : ℝ) :
    0<sourceLatitudeMomentConstant μ Q M ζ := by
  have hK := (latitudeExponentialConstant_pos (centerCoefficients (mixtureCoefficients μ) Q)).le
  unfold sourceLatitudeMomentConstant sourceLatitudeMomentPrefactor sourceLatitudeExponentCoefficient
  positivity

/-- Literal physical squared fluctuation scale, including the actual minimum degree. -/
theorem sourceLatitudeFluctuationScale_sq (n : ℕ) (μ : FiniteMixture) (r : ℝ) :
    (Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1))^2=
      ((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2) := by
  rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ)≤((n+1 : ℕ) : ℝ)),←pow_mul]
  rw [show (μ.minDegree-1)*2=2*μ.minDegree-2 by omega]

/-- Actual center-field mean controls the literal source latitude
exponent with coefficients from the fixed actual model. -/
theorem actual_source_latitude_exponent_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    let D := sourceLatitudeCorrectionConstant μ Q M
    let cQ := centerCoefficients (mixtureCoefficients μ) Q
    let t := ζ*D*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)
    ζ*D*((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+
      t*|latitudeObservableMean cQ J x (latitudeFrameAt x) r|+
      3*latitudeExponentialConstant cQ*(1+t^2)≤
      3*latitudeExponentialConstant cQ+sourceLatitudeExponentCoefficient μ Q M ζ*sourceLatitudeWeightPower n μ r := by
  dsimp only
  let D := sourceLatitudeCorrectionConstant μ Q M
  let A := centerLatitudeMeanConstant μ Q
  let K := latitudeExponentialConstant (centerCoefficients (mixtureCoefficients μ) Q)
  let v := Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)
  let w := ((n+1 : ℕ) : ℝ)*|r|^μ.minDegree
  let L := sourceLatitudeExponentCoefficient μ Q M ζ
  have hA : 0≤A := (centerLatitudeMeanConstant_pos μ Q).le
  have hK : 0≤K := (latitudeExponentialConstant_pos _).le
  have hD : 0≤D := by
    unfold D sourceLatitudeCorrectionConstant
    exact mul_nonneg (ConditionedEntrance.regressionOrderConstant_pos μ Q).le
      (by have h := (derivativeConstant_pos (centerCoefficients (mixtureCoefficients μ) Q)).le;unfold sourceLatitudeCenterConstant;linarith)
  have hv : 0≤v := by dsimp [v];positivity
  have hw : 0≤w := by dsimp [w];positivity
  have hmean := actual_center_latitudeObservableMean_uniform_bound hn μ hQ J hJ x hx hr
  have hm := mul_le_mul_of_nonneg_left hmean (show 0≤ζ*D*v by positivity)
  have hL1 : ζ*D≤L := by dsimp [L,sourceLatitudeExponentCoefficient];nlinarith [le_abs_self (ζ*D),abs_nonneg (ζ*D*A),mul_nonneg hK (sq_nonneg (ζ*D))]
  have hL2 : ζ*D*A+3*K*(ζ*D)^2≤L := by
    dsimp [L,sourceLatitudeExponentCoefficient]
    nlinarith [le_abs_self (ζ*D*A),abs_nonneg (ζ*D)]
  have hL3 : ζ*D*A≤L := by dsimp [L,sourceLatitudeExponentCoefficient];nlinarith [le_abs_self (ζ*D*A),abs_nonneg (ζ*D),mul_nonneg hK (sq_nonneg (ζ*D))]
  have hvsq := sourceLatitudeFluctuationScale_sq n μ r
  change v^2=((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2) at hvsq
  dsimp only [sourceLatitudeWeightPower]
  rw [←hvsq]
  have hgoal : ζ*D*w+(ζ*D*v)*|latitudeObservableMean (centerCoefficients (mixtureCoefficients μ) Q) J x (latitudeFrameAt x) r|+
      3*K*(1+(ζ*D*v)^2)≤3*K+L*(w+v^2+v) := by
    change (ζ*D*v)*|latitudeObservableMean (centerCoefficients (mixtureCoefficients μ) Q) J x (latitudeFrameAt x) r|≤
      (ζ*D*v)*(A*(v+1)) at hm
    nlinarith [mul_le_mul_of_nonneg_right hL1 hw,mul_le_mul_of_nonneg_right hL2 (sq_nonneg v),
      mul_le_mul_of_nonneg_right hL3 hv]
  convert hgoal using 1
  ring

/-- The actual mean-square prefactor keeps exactly its physical radial order. -/
theorem actual_center_latitude_mean_square_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    1+(latitudeObservableMean (centerCoefficients (mixtureCoefficients μ) Q) J x (latitudeFrameAt x) r)^2≤
      (1+2*(centerLatitudeMeanConstant μ Q)^2)*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2)) := by
  let A := centerLatitudeMeanConstant μ Q
  let v := Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)
  have hA := (centerLatitudeMeanConstant_pos μ Q).le
  have hv : 0≤v := by dsimp [v];positivity
  have hm := pow_le_pow_left₀ (abs_nonneg _) (actual_center_latitudeObservableMean_uniform_bound hn μ hQ J hJ x hx hr) 2
  rw [sq_abs,mul_pow] at hm
  have hvsq := sourceLatitudeFluctuationScale_sq n μ r
  change v^2=((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2) at hvsq
  rw [←hvsq]
  change 1+(latitudeObservableMean (centerCoefficients (mixtureCoefficients μ) Q) J x (latitudeFrameAt x) r)^2≤
    (1+2*A^2)*(1+v^2)
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (v-1)),sq_nonneg v]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
