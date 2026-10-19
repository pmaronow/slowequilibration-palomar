-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactValue
public import SlowEquilibration.PureResidualCoefficientSource

@[expose] public section

/-! The exact scalar factorization of the normalized proper-pure cap
latitude derivative in manuscript §9.13. -/

namespace SlowEquilibration.SphericalPureCapLatitudeFactor
noncomputable section
open Set
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
set_option autoImplicit false

def capAux (p : ℕ) (β a : ℝ) : ℝ := β*a^(p-2)*(1-a^2)

def capPolynomial (p : ℕ) (e y : ℝ) : ℝ :=
  (p:ℝ)*e*y-1-(p:ℝ)*((p:ℝ)-1)*y^2

theorem capAux_hasDerivAt (p : ℕ) (hp : 4 ≤ p) (β a : ℝ) :
    HasDerivAt (capAux p β)
      (β*a^(p-3)*(((p:ℝ)-2)-(p:ℝ)*a^2)) a := by
  have hpow : a^(p-2)=a^(p-3)*a := by
    calc
      a^(p-2)=a^((p-3)+1) := by congr 1; omega
      _=a^(p-3)*a := by rw [pow_add,pow_one]
  have hpow2 : a^(p-2)*a=a^(p-3)*a^2 := by rw [hpow]; ring
  have hcast : ((p-2:ℕ):ℝ)=(p:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    norm_num
  have hderiv := (((hasDerivAt_id a).pow (p-2)).mul
    ((hasDerivAt_const a (1:ℝ)).sub ((hasDerivAt_id a).pow 2))).const_mul β
  convert hderiv using 1
  · funext t; dsimp [capAux]; ring
  · simp only [id_eq,mul_one,zero_sub,hcast,
      show p-2-1=p-3 by omega,show 2-1=1 by omega,pow_one]
    change β*a^(p-3)*((p:ℝ)-2-(p:ℝ)*a^2) =
      β*(((p:ℝ)-2)*a^(p-3)*(1-a^2)+a^(p-2)*(-(2*a)))
    rw [hpow]
    ring

theorem sourcePureLatitudeVarianceSlope_normalized
    (p : ℕ) (hp : 4 ≤ p) (a : ℝ) :
    sourcePureLatitudeVarianceSlope p 1 a =
      -2*(p:ℝ)*((p:ℝ)-1)*a^(2*p-3)*(1-a^2) := by
  have hpow : a^(2*p-1)=a^(2*p-3)*a^2 := by
    rw [←pow_add]
    congr 1
    omega
  have hcast1 : ((2*p:ℕ):ℝ)=2*(p:ℝ) := by push_cast; ring
  have hcast2 : ((2*p-2:ℕ):ℝ)=2*(p:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*p)]
    push_cast
    ring
  unfold sourcePureLatitudeVarianceSlope
  rw [hpow,hcast2]
  ring

/-- Exact factorization of the derivative, where `e` is the source
unit-sphere critical energy and `E=e*(sqrt Q)^p` is its section value. -/
theorem sourcePureLatitudeExponent_slope_factor
    (p : ℕ) (hp : 4 ≤ p) {Q : ℝ} (hQ : 0 < Q)
    (β e a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) :
    sourcePureLatitudeExponentSlope p 1 Q β
      (e*(Real.sqrt Q)^p) a =
        a/(1-a^2)*capPolynomial p e (capAux p β a) := by
  have hq : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hs : 1-a^2 ≠ 0 := by
    apply ne_of_gt
    nlinarith [ha.1,ha.2]
  have hpow : a^(p-1)=a^(p-2)*a := by
    calc
      a^(p-1)=a^((p-2)+1) := by congr 1; omega
      _=a^(p-2)*a := by rw [pow_add,pow_one]
  have hpow2 : a^(2*p-3)=a*(a^(p-2))^2 := by
    calc
      a^(2*p-3)=a^(2*(p-2)+1) := by congr 1; omega
      _=a^(2*(p-2))*a := by rw [pow_add,pow_one]
      _=a*(a^(p-2))^2 := by rw [pow_mul]; ring
  unfold sourcePureLatitudeExponentSlope capAux capPolynomial
  rw [sourcePureLatitudeVarianceSlope_normalized p hp a]
  rw [div_pow,show (Real.sqrt Q)^p=(Real.sqrt Q)^(p-1)*Real.sqrt Q by
    rw [←pow_succ]; congr 1; omega]
  field_simp [hq,hs,ha.1.ne']
  rw [hpow,hpow2]
  ring

end
end SlowEquilibration.SphericalPureCapLatitudeFactor
