-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudePureSourceExponentialMoments

/-! Genuine quadratic source latitude moments. The source envelope is
squared before averaging, retaining all three literal radial powers. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sourceLatitudeQuadraticPower (n : ℕ) (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^2*|r|^(2*μ.minDegree)+
  ((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2)+
  ((n+1 : ℕ) : ℝ)^2*|r|^(4*μ.minDegree-4)

def sourceLatitudeQuadraticConstant (μ : FiniteMixture) (Q M ζ : ℝ) : ℝ :=
  1+2*(sourceLatitudeCorrectionConstant μ Q M)^2*sourceLatitudeMomentConstant μ Q M ζ

theorem sourceLatitudeQuadraticConstant_pos (μ : FiniteMixture) (Q M ζ : ℝ) :
    0<sourceLatitudeQuadraticConstant μ Q M ζ := by
  have hc := (sourceLatitudeMomentConstant_pos μ Q M ζ).le
  unfold sourceLatitudeQuadraticConstant
  positivity

/-- Squaring the genuine source envelope and applying the true latitude
moments gives its literal radial quadratic order, with integrability. -/
theorem latitude_source_dominated_square_exp_abs_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) {M ζ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ}
    (hr : r∈Ioo (-1 : ℝ) 1) (F : Vector (n+1)→ℝ) (hF : Continuous F)
    (hFb : ∀ᵐ u ∂latitudeLaw x (latitudeFrameAt x) r,
      |F u|≤ sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|)) :
    Integrable (fun u => (F u)^2*Real.exp (ζ*|F u|)) (latitudeLaw x (latitudeFrameAt x) r) ∧
    (∫ u,(F u)^2*Real.exp (ζ*|F u|) ∂latitudeLaw x (latitudeFrameAt x) r)≤
      sourceLatitudeQuadraticConstant μ Q M ζ*sourceLatitudeQuadraticPower n μ r*
        Real.exp (sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r) := by
  let D := sourceLatitudeCorrectionConstant μ Q M
  let a := ((n+1 : ℕ) : ℝ)*|r|^μ.minDegree
  let b := Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let V := observable cQ J x
  let E := fun u => Real.exp (ζ*|F u|)
  let ν := latitudeLaw x (latitudeFrameAt x) r
  let C := sourceLatitudeMomentConstant μ Q M ζ
  let H := Real.exp (C*sourceLatitudeWeightPower n μ r)
  have hD : 0≤D := by
    unfold D sourceLatitudeCorrectionConstant
    exact mul_nonneg (regressionOrderConstant_pos μ Q).le
      (by have h := (derivativeConstant_pos cQ).le;unfold sourceLatitudeCenterConstant;dsimp only [cQ] at h;linarith)
  have h0 := latitude_source_dominated_exp_abs_le hn μ hQ hM hζ J hJ x hx hr F hF hFb
  have h2 := latitude_source_dominated_observable_square_exp_abs_le hn μ hQ hM hζ J hJ x hx hr F hF hFb
  have hi0 : Integrable (fun u => 2*D^2*a^2*E u) ν := h0.1.const_mul _
  have hi2 : Integrable (fun u => 2*D^2*b^2*((V u)^2*E u)) ν := h2.1.const_mul _
  have hib : Integrable (fun u => 2*D^2*a^2*E u+2*D^2*b^2*((V u)^2*E u)) ν := by
    convert hi0.add hi2 using 1
  have hdom : ∀ᵐ u ∂ν,(F u)^2*E u≤2*D^2*a^2*E u+2*D^2*b^2*((V u)^2*E u) := by
    filter_upwards [hFb] with u hu
    have ht : 0≤D*(a+b*|V u|) := by dsimp [a,b];positivity
    have hs := (sq_le_sq₀ (abs_nonneg (F u)) ht).mpr hu
    rw [sq_abs] at hs
    have hh : (F u)^2≤2*D^2*a^2+2*D^2*b^2*(V u)^2 := by
      apply hs.trans
      calc
        _≤(D*(a+b*|V u|))^2+D^2*(a-b*|V u|)^2 :=
          le_add_of_nonneg_right (mul_nonneg (sq_nonneg D) (sq_nonneg _))
        _=2*D^2*a^2+2*D^2*b^2*|V u|^2 := by ring
        _=_ := by rw [sq_abs]
    apply (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq
    ring
  have hif : Integrable (fun u => (F u)^2*E u) ν := by
    apply hib.mono' (((hF.pow 2).mul ((hF.abs.const_mul ζ).rexp)).aestronglyMeasurable)
    filter_upwards [hdom] with u hu
    change ‖(F u)^2*E u‖≤_
    rw [Real.norm_of_nonneg (by dsimp only [E];positivity)]
    exact hu
  refine ⟨hif,?_⟩
  apply (integral_mono_ae hif hib hdom).trans
  have hsum : (∫ u,2*D^2*a^2*E u+2*D^2*b^2*((V u)^2*E u) ∂ν)=
      2*D^2*a^2*(∫ u,E u ∂ν)+2*D^2*b^2*(∫ u,(V u)^2*E u ∂ν) := by
    rw [integral_add hi0 hi2,integral_const_mul,integral_const_mul]
  rw [hsum]
  have hb2 : b^2=((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2) := sourceLatitudeFluctuationScale_sq n μ r
  have ha2 : a^2=((n+1 : ℕ) : ℝ)^2*|r|^(2*μ.minDegree) := by
    dsimp only [a]
    rw [mul_pow,←pow_mul,Nat.mul_comm μ.minDegree 2]
  have hmin := μ.minDegree_ge_two
  have hpow : |r|^(2*μ.minDegree-2)*|r|^(2*μ.minDegree-2)=|r|^(4*μ.minDegree-4) := by
    rw [←pow_add,show 2*μ.minDegree-2+(2*μ.minDegree-2)=4*μ.minDegree-4 by omega]
  have hraw := add_le_add
    (mul_le_mul_of_nonneg_left h0.2 (by positivity : 0≤2*D^2*a^2))
    (mul_le_mul_of_nonneg_left h2.2 (by positivity : 0≤2*D^2*b^2))
  apply hraw.trans
  have heq : 2*D^2*a^2*(C*H)+2*D^2*b^2*(C*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2))*H)=
      (2*D^2*C)*sourceLatitudeQuadraticPower n μ r*H := by
    rw [ha2,hb2]
    unfold sourceLatitudeQuadraticPower
    calc
      _=2*D^2*C*(((n+1 : ℕ) : ℝ)^2*|r|^(2*μ.minDegree)+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2)+
        ((n+1 : ℕ) : ℝ)^2*(|r|^(2*μ.minDegree-2)*|r|^(2*μ.minDegree-2)))*H := by ring
      _=_ := by rw [hpow]
  change 2*D^2*a^2*(C*H)+2*D^2*b^2*(C*(1+((n+1 : ℕ) : ℝ)*|r|^(2*μ.minDegree-2))*H)≤_
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (by unfold sourceLatitudeQuadraticPower;positivity)
  dsimp only [D,C,sourceLatitudeQuadraticConstant]
  linarith

end
end SlowEquilibration.EntranceLatitudeTangentObservable
