-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianCovarianceHighMoments
public import SlowEquilibration.GaussianVectorPolynomialMoments
public import SlowEquilibration.GaussianQuadraticTranslation

/-! Genuine uniform every-real-q Gaussian quadratic moments including the
actual mean translation and covariance perturbation from scalar covariance. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

lemma nonnegative_add_rpow_bound {a b q:ℝ} (ha:0≤a) (hb:0≤b) (hq:0≤q) :
    (a+b)^q ≤ (2:ℝ)^q*(a^q+b^q) := by
  by_cases hab:a≤b
  · calc
      _ ≤ (2*b)^q:=Real.rpow_le_rpow (add_nonneg ha hb) (by linarith) hq
      _=(2:ℝ)^q*b^q:=Real.mul_rpow (by norm_num) hb
      _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg ha q)) (by positivity)
  · calc
      _ ≤ (2*a)^q:=Real.rpow_le_rpow (add_nonneg ha hb) (by linarith) hq
      _=(2:ℝ)^q*a^q:=Real.mul_rpow (by norm_num) ha
      _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hb q)) (by positivity)

lemma nonnegative_four_rpow_bound {a b c d q:ℝ}
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hd:0≤d) (hq:0≤q) :
    (a+b+c+d)^q ≤ (4:ℝ)^q*(a^q+b^q+c^q+d^q) := by
  have h1:=nonnegative_add_rpow_bound (add_nonneg ha hb) (add_nonneg hc hd) hq
  have h2:=nonnegative_add_rpow_bound ha hb hq
  have h3:=nonnegative_add_rpow_bound hc hd hq
  calc
    _ ≤ (2:ℝ)^q*((a+b)^q+(c+d)^q):=by simpa only [add_assoc] using h1
    _ ≤ (2:ℝ)^q*((2:ℝ)^q*(a^q+b^q)+(2:ℝ)^q*(c^q+d^q)):=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)
    _=(4:ℝ)^q*(a^q+b^q+c^q+d^q):=by
      rw [show (4:ℝ)^q=(2:ℝ)^q*(2:ℝ)^q from by
        simpa only [show (2:ℝ)*2=4 by norm_num] using (Real.mul_rpow (z:=q) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤2))]
      ring

def gaussianNormRealMomentConstant (q σ A:ℝ):ℝ :=
  1+((Nat.ceil q).factorial:ℝ)*Real.exp (A+σ^2/2)

def quadraticHighMomentBound (d:ℕ) (σ K M L A q:ℝ):ℝ :=
  (4:ℝ)^q*(quadraticMomentConstant q*(quadraticFluctuationScale d (σ^2*L))^q+
    ((d:ℝ)*L*K)^q+(2*L*M)^q*gaussianNormRealMomentConstant q σ A+(L*M^2)^q)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual ordinary translated quadratic high moment, derived from
Gaussian covariance, true trace centering, and Gaussian norm moments. -/
theorem gaussian_quadratic_uniform_high_moment (μ : Measure E) [IsGaussian μ]
    (hmean:∫ x,x ∂μ=0) {σ K M L A τ:ℝ}
    (hσ:0<σ) (hK:0≤K) (hM:0≤M) (hL:0<L)
    (hcov:∀ x:E,covarianceBilin μ x x≤σ^2*‖x‖^2)
    (hCovErr:‖covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E‖≤K)
    (hscale:σ*Real.sqrt (Module.finrank ℝ E:ℝ)≤A)
    (v:E) (hv:‖v‖≤M) (S:E→L[ℝ]E)
    (hS:S.toLinearMap.IsSymmetric) (hSL:‖S‖≤L)
    (hm:0<Module.finrank ℝ E) (q:ℝ) (hq:0≤q) :
    Integrable (fun u=>|inner ℝ (u+v) (S (u+v))-τ*LinearMap.trace ℝ E S.toLinearMap|^q) μ ∧
      (∫ u,|inner ℝ (u+v) (S (u+v))-τ*LinearMap.trace ℝ E S.toLinearMap|^q ∂μ)≤
        quadraticHighMomentBound (Module.finrank ℝ E) σ K M L A q := by
  let Q:=fun u:E=>inner ℝ u (S u)
  let t:=τ*LinearMap.trace ℝ E S.toLinearMap
  let c:=∫ u,Q u ∂μ
  let ε:=(Module.finrank ℝ E:ℝ)*L*K
  have hε:0≤ε:=by dsimp only [ε];positivity
  have hQ:=centered_gaussian_quadratic_high_moment μ hmean hσ hL hcov S hS hSL hm q hq
  have hNormInt:=GaussianVectorPolynomialMoments.centered_gaussian_norm_moments μ hmean hσ hcov hscale (Nat.ceil q)
  have hNorm:=NonnegativeRealMoment.real_moment_of_integer μ (fun u:E=>‖u‖) continuous_norm.measurable
    (fun _=>norm_nonneg _) hq (Nat.ceil q) (Nat.le_ceil q) hNormInt.1
  have hNormBound:(∫ u:E,‖u‖^q ∂μ)≤gaussianNormRealMomentConstant q σ A:=
    hNorm.2.trans (add_le_add le_rfl hNormInt.2)
  have hME:|c-t|≤ε:=by
    dsimp only [c,Q,t]
    rw [quadratic_integral_eq_trace μ IsGaussian.memLp_two_id]
    have heq:LinearMap.trace ℝ E (S.comp (covarianceOperator μ)).toLinearMap-
        τ*LinearMap.trace ℝ E S.toLinearMap=
      LinearMap.trace ℝ E (S.comp (covarianceOperator μ-τ • ContinuousLinearMap.id ℝ E)).toLinearMap:=by
      rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_id]
      simp only [ContinuousLinearMap.toLinearMap_sub,ContinuousLinearMap.toLinearMap_smul,map_sub,map_smul,smul_eq_mul]
    rw [heq]
    exact (abs_trace_comp_le_dimension_norm S _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hSL (Nat.cast_nonneg _)) hCovErr (norm_nonneg _) (by positivity))
  let F:=fun u:E=>inner ℝ (u+v) (S (u+v))-t
  let R:=fun u:E=>(4:ℝ)^q*(|Q u-c|^q+ε^q+(2*L*M)^q*‖u‖^q+(L*M^2)^q)
  have hR:Integrable R μ:=
    (((hQ.1.add (integrable_const (ε^q))).add (hNorm.1.const_mul ((2*L*M)^q))).add
      (integrable_const ((L*M^2)^q))).const_mul ((4:ℝ)^q)
  have hp (u:E):|F u|^q≤R u:=by
    have hTrans:|inner ℝ (u+v) (S (u+v))-Q u|≤2*L*M*‖u‖+L*M^2:=by
      calc
        _ ≤ ‖S‖*M*(2*‖u‖+M):=quadratic_translation_abs_le S u v hM hv
        _ ≤ L*M*(2*‖u‖+M):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSL hM) (by positivity)
        _=_:=by ring
    have hab:|F u|≤|Q u-c|+ε+2*L*M*‖u‖+L*M^2:=by
      have heq:F u=(Q u-c)+(c-t)+(inner ℝ (u+v) (S (u+v))-Q u):=by dsimp only [F];ring
      rw [heq]
      exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
        (by linarith [hME,hTrans])
    calc
      _ ≤ (|Q u-c|+ε+2*L*M*‖u‖+L*M^2)^q:=Real.rpow_le_rpow (abs_nonneg _) hab hq
      _ ≤ (4:ℝ)^q*(|Q u-c|^q+ε^q+(2*L*M*‖u‖)^q+(L*M^2)^q):=
        nonnegative_four_rpow_bound (abs_nonneg _) hε (by positivity) (by positivity) hq
      _=R u:=by rw [Real.mul_rpow (by positivity : 0≤2*L*M) (norm_nonneg _)]
  have hF:Integrable (fun u=>|F u|^q) μ:=hR.mono' (by dsimp only [F];fun_prop)
    (ae_of_all _ (fun u=>by rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)];exact hp u))
  refine ⟨hF,?_⟩
  have hI:=integral_mono hF hR hp
  change (∫ u,|F u|^q ∂μ)≤_ at hI ⊢
  have hRI:(∫ u,R u ∂μ)=(4:ℝ)^q*((∫ u,|Q u-c|^q ∂μ)+ε^q+
      (2*L*M)^q*(∫ u:E,‖u‖^q ∂μ)+(L*M^2)^q):=by
    dsimp only [R]
    rw [integral_const_mul]
    have hQi:Integrable (fun u:E=>|Q u-c|^q) μ:=hQ.1
    have hAdd1:=integral_add (f:=fun u:E=>|Q u-c|^q+ε^q+(2*L*M)^q*‖u‖^q)
      (g:=fun _u:E=>(L*M^2)^q)
      ((hQi.add (integrable_const (ε^q))).add (hNorm.1.const_mul ((2*L*M)^q)))
      (integrable_const ((L*M^2)^q))
    have hAdd2:=integral_add (f:=fun u:E=>|Q u-c|^q+ε^q) (g:=fun u:E=>(2*L*M)^q*‖u‖^q)
      (hQi.add (integrable_const (ε^q))) (hNorm.1.const_mul ((2*L*M)^q))
    have hAdd3:=integral_add (f:=fun u:E=>|Q u-c|^q) (g:=fun _u:E=>ε^q) hQi (integrable_const (ε^q))
    rw [hAdd1,hAdd2,hAdd3,integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hRI] at hI
  exact hI.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hQ.2 le_rfl)
      (mul_le_mul_of_nonneg_left hNormBound (by positivity))) le_rfl) (by positivity))

end
end SlowEquilibration.GaussianQuadraticVariance
