-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactSign

@[expose] public section

/-! The literal proper-pure conditional latitude variance `v(a)` from the
source Palm upper-bound calculation, with exact polynomial derivatives. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeVariance
noncomputable section
open Set
set_option autoImplicit false

def sourcePureLatitudeVariance (p : ℕ) (alpha a : ℝ) : ℝ :=
  alpha*(1-a^(2*p)-(p:ℝ)*a^(2*p-2)*(1-a^2))

theorem sourcePureLatitudeVariance_eq_poly
    (p : ℕ) (hp : 2 ≤ p) (alpha a : ℝ) :
    sourcePureLatitudeVariance p alpha a =
      alpha*(1+((p:ℝ)-1)*a^(2*p)-(p:ℝ)*a^(2*p-2)) := by
  have hpow : a^(2*p-2)*a^2=a^(2*p) := by
    rw [← pow_add,Nat.sub_add_cancel (by omega : 2 ≤ 2*p)]
  calc
    sourcePureLatitudeVariance p alpha a =
        alpha*(1-a^(2*p)-(p:ℝ)*a^(2*p-2)+
          (p:ℝ)*(a^(2*p-2)*a^2)) := by
          unfold sourcePureLatitudeVariance
          ring
    _ = _ := by rw [hpow]; ring

def sourcePureLatitudeVarianceSlope (p : ℕ) (alpha a : ℝ) : ℝ :=
  alpha*((p:ℝ)-1)*(2*p:ℝ)*a^(2*p-1)-
    alpha*(p:ℝ)*(2*p-2:ℕ)*a^(2*p-3)

theorem sourcePureLatitudeVariance_hasDerivAt
    (p : ℕ) (hp : 2 ≤ p) (alpha a : ℝ) :
    HasDerivAt (sourcePureLatitudeVariance p alpha)
      (sourcePureLatitudeVarianceSlope p alpha a) a := by
  have hfun : sourcePureLatitudeVariance p alpha =
      fun t : ℝ => alpha*(1+((p:ℝ)-1)*t^(2*p)-(p:ℝ)*t^(2*p-2)) := by
    funext t
    exact sourcePureLatitudeVariance_eq_poly p hp alpha t
  rw [hfun]
  have h1 := (hasDerivAt_id a).pow (2*p)
  have h2 := (hasDerivAt_id a).pow (2*p-2)
  have hd := ((hasDerivAt_const a (1:ℝ)).add
    (h1.const_mul ((p:ℝ)-1))).sub (h2.const_mul (p:ℝ))
  convert hd.const_mul alpha using 1
  · rfl
  · unfold sourcePureLatitudeVarianceSlope
    have hcast : ((2*p-2:ℕ):ℝ)=2*(p:ℝ)-2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2*p)]
      push_cast
      ring
    have hcast2 : ((2*p:ℕ):ℝ)=2*(p:ℝ) := by push_cast; ring
    have hsub : 2*p-2-1=2*p-3 := by omega
    simp only [id_eq,mul_one,zero_add,hsub]
    rw [hcast,hcast2]
    ring

def sourcePureLatitudeVarianceCurvature (p : ℕ) (alpha a : ℝ) : ℝ :=
  alpha*((p:ℝ)-1)*(2*p:ℝ)*(2*p-1:ℕ)*a^(2*p-2)-
    alpha*(p:ℝ)*(2*p-2:ℕ)*(2*p-3:ℕ)*a^(2*p-4)

theorem sourcePureLatitudeVarianceSlope_hasDerivAt
    (p : ℕ) (hp : 2 ≤ p) (alpha a : ℝ) :
    HasDerivAt (sourcePureLatitudeVarianceSlope p alpha)
      (sourcePureLatitudeVarianceCurvature p alpha a) a := by
  have h1 := (hasDerivAt_id a).pow (2*p-1)
  have h2 := (hasDerivAt_id a).pow (2*p-3)
  have hd := (h1.const_mul (alpha*((p:ℝ)-1)*(2*p:ℝ))).sub
    (h2.const_mul (alpha*(p:ℝ)*(2*p-2:ℕ)))
  convert hd using 1
  · rfl
  · unfold sourcePureLatitudeVarianceCurvature
    have hsub1 : 2*p-1-1=2*p-2 := by omega
    have hsub2 : 2*p-3-1=2*p-4 := by omega
    simp only [id_eq,mul_one,hsub1,hsub2]
    ring

theorem sourcePureLatitudeVariance_second_deriv
    (p : ℕ) (hp : 2 ≤ p) (alpha a : ℝ) :
    deriv (deriv (sourcePureLatitudeVariance p alpha)) a =
      sourcePureLatitudeVarianceCurvature p alpha a := by
  have hfirst : deriv (sourcePureLatitudeVariance p alpha) =
      sourcePureLatitudeVarianceSlope p alpha := by
    funext t
    exact (sourcePureLatitudeVariance_hasDerivAt p hp alpha t).deriv
  rw [hfirst]
  exact (sourcePureLatitudeVarianceSlope_hasDerivAt p hp alpha a).deriv

/-- Exact source variance-curvature formula at the contact latitude. -/
theorem sourcePureLatitudeVariance_curvature_at_contact
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    sourcePureLatitudeVarianceCurvature p alpha (Real.sqrt Q) =
      2*alpha*(p:ℝ)*((p:ℝ)-1)*Q^(p-2)*
        ((((2*p:ℕ):ℝ)-1)*Q-(((2*p:ℕ):ℝ)-3)) := by
  let q := Real.sqrt Q
  have hq2 : q^2=Q := Real.sq_sqrt hQ.le
  have hpow1 : q^(2*p-2)=q^(2*p-4)*Q := by
    rw [show 2*p-2=(2*p-4)+2 by omega,pow_add,hq2]
  have hpow2 : q^(2*p-4)=Q^(p-2) := by
    calc
      q^(2*p-4)=q^(2*(p-2)) := by congr 1; omega
      _=(q^2)^(p-2) := by rw [pow_mul]
      _=Q^(p-2) := by rw [hq2]
  have hc2 : ((2*p-2:ℕ):ℝ)=((2*p:ℕ):ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*p)]
    norm_num
  have hc3 : ((2*p-3:ℕ):ℝ)=((2*p:ℕ):ℝ)-3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 2*p)]
    norm_num
  have hc1 : ((2*p-1:ℕ):ℝ)=((2*p:ℕ):ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*p)]
    norm_num
  have hcp : ((2*p:ℕ):ℝ)=2*(p:ℝ) := by push_cast; ring
  dsimp [sourcePureLatitudeVarianceCurvature]
  rw [hpow1,hpow2,hc1,hc2,hc3,hcp]
  ring

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeVariance
