-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeCenterMean

/-! Genuine absolute and exponentially weighted second moments of the
sampled field's centered latitude tangent observable. The exact actual
Gaussian-radius concentration errors are retained explicitly. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual fixed-field centered latitude tangent observable. -/
def centeredLatitudeObservable {n P : ℕ} (c : Degree P→ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (r : ℝ) (v : Vector (n+1)) : ℝ :=
  observable c J u v-latitudeObservableMean c J u (latitudeFrameAt u) r

/-- The already derived exact actual MGF bound, with radius-tail errors. -/
def latitudeObservableMGFEnvelope {P : ℕ} (n : ℕ) (c : Degree P→ℝ) (t : ℝ) : ℝ :=
  Real.exp (|t| *(2*derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/8))+
    288*(derivativeConstant c)^2*t^2)+
  Real.exp (2*derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ)*|t|-(n : ℝ)/8)

private theorem centeredLatitudeObservable_bounded {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    ∀ᵐ v ∂latitudeLaw u (latitudeFrameAt u) r,
      |centeredLatitudeObservable c J u r v|≤2*derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ) := by
  have hv : ∀ᵐ v ∂latitudeLaw u (latitudeFrameAt u) r,
      ‖observable c J u v‖≤derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ) := by
    filter_upwards [latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr] with v hvs
    rw [Real.norm_eq_abs]
    exact observable_abs_le (by omega) c J hJ u v hu hvs.1
  have hm := norm_integral_le_of_norm_le_const hv
  simp only [Real.norm_eq_abs,probReal_univ,mul_one] at hm
  filter_upwards [hv] with v hvs
  unfold centeredLatitudeObservable latitudeObservableMean
  have ha : |observable c J u v-∫ w,observable c J u w ∂latitudeLaw u (latitudeFrameAt u) r|≤
      |observable c J u v|+|∫ w,observable c J u w ∂latitudeLaw u (latitudeFrameAt u) r| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (observable c J u v) 0
      (∫ w,observable c J u w ∂latitudeLaw u (latitudeFrameAt u) r)
  rw [Real.norm_eq_abs] at hvs
  linarith

/-- True exponential absolute moments are integrable under the actual
latitude law; no exponential-moment hypothesis is needed. -/
theorem centeredLatitudeObservable_exp_abs_integrable {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) (t : ℝ) :
    Integrable (fun v => Real.exp (t*|centeredLatitudeObservable c J u r v|))
      (latitudeLaw u (latitudeFrameAt u) r) := by
  have hz := centeredLatitudeObservable_bounded hn c J hJ u hu hr
  have hcont : Continuous (centeredLatitudeObservable c J u r) :=
    (observable_continuous c J u).sub continuous_const
  apply Integrable.of_bound (hcont.abs.const_mul t |>.rexp.aestronglyMeasurable)
    (Real.exp (|t| *(2*derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ))))
  filter_upwards [hz] with v hv
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t*|centeredLatitudeObservable c J u r v|)).trans
    (by rw [abs_mul,abs_abs];exact mul_le_mul_of_nonneg_left hv (abs_nonneg t))

private theorem centeredLatitudeObservable_exp_integrable {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) (t : ℝ) :
    Integrable (fun v => Real.exp (t*centeredLatitudeObservable c J u r v))
      (latitudeLaw u (latitudeFrameAt u) r) := by
  apply (centeredLatitudeObservable_exp_abs_integrable hn c J hJ u hu hr |t|).mono' (by
    have hcont : Continuous (centeredLatitudeObservable c J u r) := (observable_continuous c J u).sub continuous_const
    exact (hcont.const_mul t).rexp.aestronglyMeasurable)
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  simpa only [abs_mul] using le_abs_self (t*centeredLatitudeObservable c J u r v)

/-- Absolute centered exponential moment from the actual positive and
negative MGF, retaining their honest radius errors. -/
theorem actual_latitude_centered_exp_abs_le {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1)
    (t : ℝ) :
    (∫ v,Real.exp (t*|centeredLatitudeObservable c J u r v|) ∂latitudeLaw u (latitudeFrameAt u) r)≤
      2*latitudeObservableMGFEnvelope n c t := by
  have hp := centeredLatitudeObservable_exp_integrable hn c J hJ u hu hr t
  have hm := centeredLatitudeObservable_exp_integrable hn c J hJ u hu hr (-t)
  have ha := centeredLatitudeObservable_exp_abs_integrable hn c J hJ u hu hr t
  have his : Integrable (fun v => Real.exp (t*centeredLatitudeObservable c J u r v)+
      Real.exp (-t*centeredLatitudeObservable c J u r v)) (latitudeLaw u (latitudeFrameAt u) r) := by
    convert hp.add hm using 1
  have hpt := observable_centered_mgf_le hn c J hJ u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr t
  have hmt := observable_centered_mgf_le hn c J hJ u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr (-t)
  change (∫ v,Real.exp (t*centeredLatitudeObservable c J u r v) ∂latitudeLaw u (latitudeFrameAt u) r)≤
    latitudeObservableMGFEnvelope n c t at hpt
  change (∫ v,Real.exp (-t*centeredLatitudeObservable c J u r v) ∂latitudeLaw u (latitudeFrameAt u) r)≤
    latitudeObservableMGFEnvelope n c (-t) at hmt
  have he : latitudeObservableMGFEnvelope n c (-t)=latitudeObservableMGFEnvelope n c t := by
    simp only [latitudeObservableMGFEnvelope,abs_neg,neg_sq]
  rw [he] at hmt
  calc
    _≤∫ v,Real.exp (t*centeredLatitudeObservable c J u r v)+Real.exp (-t*centeredLatitudeObservable c J u r v)
        ∂latitudeLaw u (latitudeFrameAt u) r := by
      apply integral_mono_ae ha his
      filter_upwards [] with v
      by_cases hz : 0≤centeredLatitudeObservable c J u r v
      · rw [abs_of_nonneg hz]
        linarith [Real.exp_pos (-t*centeredLatitudeObservable c J u r v)]
      · rw [abs_of_neg (lt_of_not_ge hz)]
        rw [show t*(-centeredLatitudeObservable c J u r v)=(-t)*centeredLatitudeObservable c J u r v by ring]
        linarith [Real.exp_pos (t*centeredLatitudeObservable c J u r v)]
    _≤_ := by
      have hsplit : (∫ v,Real.exp (t*centeredLatitudeObservable c J u r v)+
          Real.exp (-t*centeredLatitudeObservable c J u r v) ∂latitudeLaw u (latitudeFrameAt u) r)=
          (∫ v,Real.exp (t*centeredLatitudeObservable c J u r v) ∂latitudeLaw u (latitudeFrameAt u) r)+
          (∫ v,Real.exp (-t*centeredLatitudeObservable c J u r v) ∂latitudeLaw u (latitudeFrameAt u) r) := by
        convert integral_add hp hm using 1
      rw [hsplit]
      linarith

/-- The actual centered weighted second moment requires no fourth-moment
or subGaussian premise: a literal exponential inequality and the true
MGF give it directly. -/
theorem actual_latitude_centered_second_exp_abs_le {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1)
    (t : ℝ) :
    Integrable (fun v => (centeredLatitudeObservable c J u r v)^2*
      Real.exp (t*|centeredLatitudeObservable c J u r v|)) (latitudeLaw u (latitudeFrameAt u) r) ∧
    (∫ v,(centeredLatitudeObservable c J u r v)^2*Real.exp (t*|centeredLatitudeObservable c J u r v|)
      ∂latitudeLaw u (latitudeFrameAt u) r)≤4*latitudeObservableMGFEnvelope n c (t+1) := by
  have he (z : ℝ) : z^2*Real.exp (t*|z|)≤2*Real.exp ((t+1)*|z|) := by
    have hz : z^2/2≤Real.exp |z| := by simpa only [sq_abs,Nat.factorial_two,Nat.cast_ofNat] using Real.pow_div_factorial_le_exp |z| (abs_nonneg z) 2
    have h := mul_le_mul_of_nonneg_right (show z^2≤2*Real.exp |z| by linarith) (Real.exp_pos (t*|z|)).le
    apply h.trans_eq
    rw [mul_assoc,←Real.exp_add]
    congr 1
    congr 1
    ring
  have hi := (centeredLatitudeObservable_exp_abs_integrable hn c J hJ u hu hr (t+1)).const_mul 2
  have hf : Integrable (fun v => (centeredLatitudeObservable c J u r v)^2*
      Real.exp (t*|centeredLatitudeObservable c J u r v|)) (latitudeLaw u (latitudeFrameAt u) r) := by
    apply hi.mono' (by
      have hcont : Continuous (centeredLatitudeObservable c J u r) := (observable_continuous c J u).sub continuous_const
      exact ((hcont.pow 2).mul (hcont.abs.const_mul t |>.rexp)).aestronglyMeasurable)
    filter_upwards [] with v
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact he _
  refine ⟨hf,?_⟩
  apply (integral_mono_ae hf hi (ae_of_all _ (fun v => he _))).trans
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (actual_latitude_centered_exp_abs_le hn c J hJ u hu hr (t+1)) (by norm_num : (0 : ℝ)≤2)
  apply h.trans_eq
  ring

end
end SlowEquilibration.EntranceLatitudeTangentObservable
