-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeUniformExponentialMoments

/-! Actual uncentered sampled-field latitude exponential moments. The
mean is the genuine latitude integral; no asserted mean or covariance law
is an input to these moment identities. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem observable_abs_le_centered_mean {n P : ℕ} (c : Degree P→ℝ)
    (J : Disorder (n+1) P) (u : Vector (n+1)) (r : ℝ) (v : Vector (n+1)) :
    |observable c J u v|≤|centeredLatitudeObservable c J u r v|+
      |latitudeObservableMean c J u (latitudeFrameAt u) r| := by
  have h : observable c J u v=centeredLatitudeObservable c J u r v+
      latitudeObservableMean c J u (latitudeFrameAt u) r := by unfold centeredLatitudeObservable;ring
  rw [h]
  exact abs_add_le _ _

/-- True absolute exponential integrability follows from actual sample
regularity and actual latitude support. -/
theorem latitudeObservable_exp_abs_integrable {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) (t : ℝ) :
    Integrable (fun v => Real.exp (t*|observable c J u v|)) (latitudeLaw u (latitudeFrameAt u) r) := by
  apply Integrable.of_bound ((observable_continuous c J u).abs.const_mul t |>.rexp.aestronglyMeasurable)
    (Real.exp (|t| *(derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ))))
  filter_upwards [latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr] with v hv
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  apply (le_abs_self (t*|observable c J u v|)).trans
  rw [abs_mul,abs_abs]
  exact mul_le_mul_of_nonneg_left (observable_abs_le (by omega) c J hJ u v hu hv.1) (abs_nonneg t)

/-- Actual uncentered exponential moment retains its actual mean and
has a genuine dimension-uniform centered fluctuation envelope. -/
theorem actual_latitude_exp_abs_le {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1)
    {t : ℝ} (ht : 0≤t) :
    (∫ v,Real.exp (t*|observable c J u v|) ∂latitudeLaw u (latitudeFrameAt u) r)≤
      4*Real.exp (t*|latitudeObservableMean c J u (latitudeFrameAt u) r|+
        latitudeExponentialConstant c*(1+t^2)) := by
  let m := latitudeObservableMean c J u (latitudeFrameAt u) r
  have hi := latitudeObservable_exp_abs_integrable hn c J hJ u hu hr t
  have hzi := centeredLatitudeObservable_exp_abs_integrable hn c J hJ u hu hr t
  have hib : Integrable (fun v => Real.exp (t*|m|)*Real.exp (t*|centeredLatitudeObservable c J u r v|))
      (latitudeLaw u (latitudeFrameAt u) r) := hzi.const_mul _
  calc
    _≤∫ v,Real.exp (t*|m|)*Real.exp (t*|centeredLatitudeObservable c J u r v|)
        ∂latitudeLaw u (latitudeFrameAt u) r := by
      apply integral_mono_ae hi hib
      filter_upwards [] with v
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (observable_abs_le_centered_mean c J u r v) ht
      dsimp only [m]
      linarith
    _=Real.exp (t*|m|)*(∫ v,Real.exp (t*|centeredLatitudeObservable c J u r v|)
        ∂latitudeLaw u (latitudeFrameAt u) r) := integral_const_mul _ _
    _≤_ := by
      apply (mul_le_mul_of_nonneg_left (actual_latitude_centered_exp_abs_uniform_le hn c J hJ u hu hr t)
        (Real.exp_pos _).le).trans_eq
      rw [mul_left_comm,←Real.exp_add]

/-- Genuine uncentered weighted second moment, derived from its literal
centered variable and actual latitude mean. -/
theorem actual_latitude_second_exp_abs_le {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1)
    {t : ℝ} (ht : 0≤t) :
    Integrable (fun v => (observable c J u v)^2*Real.exp (t*|observable c J u v|))
      (latitudeLaw u (latitudeFrameAt u) r) ∧
    (∫ v,(observable c J u v)^2*Real.exp (t*|observable c J u v|) ∂latitudeLaw u (latitudeFrameAt u) r)≤
      24*(1+(latitudeObservableMean c J u (latitudeFrameAt u) r)^2)*
        Real.exp (t*|latitudeObservableMean c J u (latitudeFrameAt u) r|+3*latitudeExponentialConstant c*(1+t^2)) := by
  let m := latitudeObservableMean c J u (latitudeFrameAt u) r
  let Z := centeredLatitudeObservable c J u r
  let ν := latitudeLaw u (latitudeFrameAt u) r
  have hiZ := (actual_latitude_centered_second_exp_abs_le hn c J hJ u hu hr t).1
  have hiE := centeredLatitudeObservable_exp_abs_integrable hn c J hJ u hu hr t
  have hdom (v : Vector (n+1)) : (observable c J u v)^2*Real.exp (t*|observable c J u v|)≤
      2*Real.exp (t*|m|)*((Z v)^2*Real.exp (t*|Z v|)+m^2*Real.exp (t*|Z v|)) := by
    have ha := observable_abs_le_centered_mean c J u r v
    have hv : observable c J u v=Z v+m := by dsimp only [Z,m,centeredLatitudeObservable];ring
    have hs : (observable c J u v)^2≤2*((Z v)^2+m^2) := by rw [hv];nlinarith [sq_nonneg (Z v-m)]
    have he : Real.exp (t*|observable c J u v|)≤Real.exp (t*|m|)*Real.exp (t*|Z v|) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left ha ht
      dsimp only [m,Z]
      linarith
    apply (mul_le_mul hs he (Real.exp_pos _).le (by positivity)).trans_eq
    ring
  have hib : Integrable (fun v => 2*Real.exp (t*|m|)*
      ((Z v)^2*Real.exp (t*|Z v|)+m^2*Real.exp (t*|Z v|))) ν := by
    convert (hiZ.add (hiE.const_mul (m^2))).const_mul (2*Real.exp (t*|m|)) using 1
  have hif : Integrable (fun v => (observable c J u v)^2*Real.exp (t*|observable c J u v|)) ν := by
    apply hib.mono' (by
      have hc := observable_continuous c J u
      exact ((hc.pow 2).mul (hc.abs.const_mul t |>.rexp)).aestronglyMeasurable)
    filter_upwards [] with v
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact hdom v
  refine ⟨hif,?_⟩
  apply (integral_mono_ae hif hib (ae_of_all _ hdom)).trans
  have hsplit : (∫ v,2*Real.exp (t*|m|)*((Z v)^2*Real.exp (t*|Z v|)+m^2*Real.exp (t*|Z v|)) ∂ν)=
      2*Real.exp (t*|m|)*((∫ v,(Z v)^2*Real.exp (t*|Z v|) ∂ν)+m^2*(∫ v,Real.exp (t*|Z v|) ∂ν)) := by
    rw [integral_const_mul]
    congr 1
    have hh := integral_add hiZ (hiE.const_mul (m^2))
    convert hh using 1
    rw [integral_const_mul]
  rw [hsplit]
  have hZ := actual_latitude_centered_second_exp_abs_uniform_le hn c J hJ u hu hr t
  have hE := actual_latitude_centered_exp_abs_uniform_le hn c J hJ u hu hr t
  have hEm : 4*Real.exp (latitudeExponentialConstant c*(1+t^2))≤
      4*Real.exp (3*latitudeExponentialConstant c*(1+t^2)) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    have hc := (latitudeExponentialConstant_pos c).le
    nlinarith [mul_nonneg hc (sq_nonneg t)]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hZ
    (mul_le_mul_of_nonneg_left (hE.trans hEm) (sq_nonneg m))) (show 0≤2*Real.exp (t*|m|) by positivity)
  apply hh.trans
  have hp0 : 0≤Real.exp (t*|m|)*Real.exp (3*latitudeExponentialConstant c*(1+t^2)) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hp2 := mul_nonneg (sq_nonneg m) hp0
  dsimp only [m] at hp0 hp2 ⊢
  rw [Real.exp_add]
  nlinarith [hp0,hp2]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
