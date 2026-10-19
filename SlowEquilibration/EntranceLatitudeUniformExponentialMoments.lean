-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeAbsoluteMoments

/-! The actual Gaussian-radius errors in latitude concentration absorb
into true model-only absolute exponential moment envelopes. Completing
the square makes the result uniform in dimension and all real parameters. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeExponentialConstant {P : ℕ} (c : Degree P→ℝ) : ℝ :=
  1000*(1+(derivativeConstant c)^2)

theorem latitudeExponentialConstant_pos {P : ℕ} (c : Degree P→ℝ) :
    0<latitudeExponentialConstant c := by unfold latitudeExponentialConstant;positivity

private theorem sqrt_dimension_exp_decay_le (n : ℕ) :
    Real.sqrt ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/8)≤3 := by
  have hn : ((n+1 : ℕ) : ℝ)≤9*Real.exp ((n : ℝ)/4) := by
    simp only [Nat.cast_add,Nat.cast_one]
    linarith [Real.add_one_le_exp ((n : ℝ)/4),(Nat.cast_nonneg n : (0 : ℝ)≤(n : ℝ))]
  have he : ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/4)≤9 := by
    apply (mul_le_mul_of_nonneg_right hn (Real.exp_pos (-(n : ℝ)/4)).le).trans_eq
    rw [mul_assoc,←Real.exp_add]
    rw [show (n : ℝ)/4+(-(n : ℝ))/4=0 by ring,Real.exp_zero,mul_one]
  have hs : (Real.sqrt ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/8))^2=
      ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/4) := by
    rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ)≤((n+1 : ℕ) : ℝ)),←Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  nlinarith [hs,mul_nonneg (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ)) (Real.exp_pos (-(n : ℝ)/8)).le]

/-- Both genuine actual concentration terms have a true dimension-uniform
quadratic exponential bound. Radius-tail errors are proved away algebraically. -/
theorem latitudeObservableMGFEnvelope_uniform_le {P : ℕ} (n : ℕ) (c : Degree P→ℝ) (t : ℝ) :
    latitudeObservableMGFEnvelope n c t≤2*Real.exp (latitudeExponentialConstant c*(1+t^2)) := by
  let C := derivativeConstant c
  have hC : 0≤C := (derivativeConstant_pos c).le
  have hdecay : 2*C*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/8)≤6*C := by
    have h := mul_le_mul_of_nonneg_left (sqrt_dimension_exp_decay_le n) (show 0≤2*C by positivity)
    convert h using 1 <;> ring
  have hm : |t| *(2*C*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.exp (-(n : ℝ)/8))+288*C^2*t^2≤
      latitudeExponentialConstant c*(1+t^2) := by
    apply (add_le_add (mul_le_mul_of_nonneg_left hdecay (abs_nonneg t)) le_rfl).trans
    unfold latitudeExponentialConstant
    change |t| *(6*C)+288*C^2*t^2≤1000*(1+C^2)*(1+t^2)
    nlinarith [sq_nonneg (C-|t|),sq_abs t,sq_nonneg t,mul_nonneg (sq_nonneg C) (sq_nonneg t)]
  have he : 2*C*Real.sqrt ((n+1 : ℕ) : ℝ)*|t|-(n : ℝ)/8≤
      latitudeExponentialConstant c*(1+t^2) := by
    unfold latitudeExponentialConstant
    change 2*C*Real.sqrt ((n+1 : ℕ) : ℝ)*|t|-(n : ℝ)/8≤1000*(1+C^2)*(1+t^2)
    have hs := sq_nonneg (4*C*|t|-Real.sqrt ((n+1 : ℕ) : ℝ)/4)
    have hn : ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 := by simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [Real.sq_sqrt (show (0 : ℝ)≤((n+1 : ℕ) : ℝ) by positivity),hn,sq_abs t,
      (Nat.cast_nonneg n : (0 : ℝ)≤(n : ℝ)),sq_nonneg t,mul_nonneg (sq_nonneg C) (sq_nonneg t)]
  unfold latitudeObservableMGFEnvelope
  apply (add_le_add (Real.exp_le_exp.mpr hm) (Real.exp_le_exp.mpr he)).trans_eq
  ring

/-- Genuine actual centered absolute exponential moments with a fixed
model-only envelope, uniform in dimension and the field-selected axis. -/
theorem actual_latitude_centered_exp_abs_uniform_le {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) (t : ℝ) :
    (∫ v,Real.exp (t*|centeredLatitudeObservable c J u r v|) ∂latitudeLaw u (latitudeFrameAt u) r)≤
      4*Real.exp (latitudeExponentialConstant c*(1+t^2)) := by
  apply (actual_latitude_centered_exp_abs_le hn c J hJ u hu hr t).trans
  apply (mul_le_mul_of_nonneg_left (latitudeObservableMGFEnvelope_uniform_le n c t) (by norm_num : (0 : ℝ)≤2)).trans_eq
  ring

/-- The true actual weighted centered second moment has the same model
scope and no supplied fourth moment or subGaussian law. -/
theorem actual_latitude_centered_second_exp_abs_uniform_le {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) (t : ℝ) :
    (∫ v,(centeredLatitudeObservable c J u r v)^2*Real.exp (t*|centeredLatitudeObservable c J u r v|)
      ∂latitudeLaw u (latitudeFrameAt u) r)≤
      8*Real.exp (3*latitudeExponentialConstant c*(1+t^2)) := by
  apply (actual_latitude_centered_second_exp_abs_le hn c J hJ u hu hr t).2.trans
  apply (mul_le_mul_of_nonneg_left (latitudeObservableMGFEnvelope_uniform_le n c (t+1))
    (by norm_num : (0 : ℝ)≤4)).trans
  have hpow : 1+(t+1)^2≤3*(1+t^2) := by nlinarith [sq_nonneg (t-1),sq_nonneg t]
  have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hpow (latitudeExponentialConstant_pos c).le)) (by norm_num : (0 : ℝ)≤8)
  rw [show latitudeExponentialConstant c*(3*(1+t^2))=3*latitudeExponentialConstant c*(1+t^2) by ring] at h
  convert h using 1
  ring

end
end SlowEquilibration.EntranceLatitudeTangentObservable
