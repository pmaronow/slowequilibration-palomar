-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianTranslatedQuadraticHighMoments

/-! Deterministic simplification of genuine Gaussian row high moments at
physical variance b/N, retaining the exact min-degree overlap exponent. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def physicalQuadraticMomentConstant (b C D L q:ℝ):ℝ :=
  (4:ℝ)^q*(quadraticMomentConstant q*(4*b*L)^q+(L*C)^q+
    (2*L*D)^q*gaussianNormRealMomentConstant q (Real.sqrt b) (Real.sqrt b)+(L*D^2)^q)

/-- The genuine row moment bound has the sharp physical scale
`r^(d−2)+N^(-1/2)` at every fixed real q, without degrading its overlap order. -/
theorem quadraticHighMomentBound_physical_rate {N m d:ℕ}
    (hN:0<N) (hmN:m≤N) {b C D L r q:ℝ}
    (hb:0≤b) (hC:0≤C) (hD:0≤D) (hL:0≤L) (hr:0≤r) (hr1:r≤1) (hq:0≤q) :
    quadraticHighMomentBound m (Real.sqrt (b/(N:ℝ)))
      (C/(N:ℝ)*r^(2*(d-2))) (D*r^(d-2)) L (Real.sqrt b) q ≤
      physicalQuadraticMomentConstant b C D L q*(r^(d-2)+1/Real.sqrt (N:ℝ))^q := by
  have hNR:0<(N:ℝ):=Nat.cast_pos.mpr hN
  have hsN:0<Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr hNR
  have hsN2:(Real.sqrt (N:ℝ))^2=(N:ℝ):=Real.sq_sqrt hNR.le
  let a:=r^(d-2)
  let ε:=a+1/Real.sqrt (N:ℝ)
  have ha0:0≤a:=pow_nonneg hr _
  have ha1:a≤1:=pow_le_one₀ hr hr1
  have ha2:a^2≤a:=by nlinarith
  have hε0:0≤ε:=by dsimp only [ε];positivity
  have haε:a≤ε:=le_add_of_nonneg_right (by positivity)
  have hInvε:1/Real.sqrt (N:ℝ)≤ε:=le_add_of_nonneg_left ha0
  have hσ2:(Real.sqrt (b/(N:ℝ)))^2=b/(N:ℝ):=Real.sq_sqrt (div_nonneg hb hNR.le)
  have hσb:b/(N:ℝ)≤b:=by
    apply (div_le_iff₀ hNR).mpr
    have hOne:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne hb
  have hNormC:gaussianNormRealMomentConstant q (Real.sqrt (b/(N:ℝ))) (Real.sqrt b)≤
      gaussianNormRealMomentConstant q (Real.sqrt b) (Real.sqrt b):=by
    unfold gaussianNormRealMomentConstant
    rw [hσ2,Real.sq_sqrt hb]
    gcongr
  have hScale:quadraticFluctuationScale m ((Real.sqrt (b/(N:ℝ)))^2*L)≤(4*b*L)*ε:=by
    unfold quadraticFluctuationScale
    rw [hσ2]
    calc
      _ ≤ 4*(b/(N:ℝ)*L)*Real.sqrt (N:ℝ):=by
        gcongr
      _=(4*b*L)*(1/Real.sqrt (N:ℝ)):=by
        field_simp
        nlinarith [congrArg (fun z:ℝ=>4*b*L*z) hsN2]
      _ ≤ _:=mul_le_mul_of_nonneg_left hInvε (by positivity)
  have hCovScale:(m:ℝ)*L*(C/(N:ℝ)*r^(2*(d-2)))≤(L*C)*ε:=by
    rw [show r^(2*(d-2))=a^2 by dsimp only [a];rw [pow_mul];ring]
    calc
      _ ≤ (N:ℝ)*L*(C/(N:ℝ)*a^2):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hmN) hL) (by positivity)
      _=(L*C)*a^2:=by field_simp
      _ ≤ (L*C)*a:=mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ ≤ _:=mul_le_mul_of_nonneg_left haε (by positivity)
  have hCrossScale:2*L*(D*r^(d-2))≤(2*L*D)*ε:=by
    change 2*L*(D*a)≤_
    calc
      _=(2*L*D)*a:=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left haε (by positivity)
  have hConstScale:L*(D*r^(d-2))^2≤(L*D^2)*ε:=by
    change L*(D*a)^2≤_
    calc
      _=(L*D^2)*a^2:=by ring
      _ ≤ (L*D^2)*a:=mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ ≤ _:=mul_le_mul_of_nonneg_left haε (by positivity)
  have hScaleQ:=Real.rpow_le_rpow (by unfold quadraticFluctuationScale;positivity) hScale hq
  have hCovQ:=Real.rpow_le_rpow (by positivity : 0≤(m:ℝ)*L*(C/(N:ℝ)*r^(2*(d-2)))) hCovScale hq
  have hCrossQ:=Real.rpow_le_rpow (by positivity : 0≤2*L*(D*r^(d-2))) hCrossScale hq
  have hConstQ:=Real.rpow_le_rpow (by positivity : 0≤L*(D*r^(d-2))^2) hConstScale hq
  rw [Real.mul_rpow (by positivity) hε0] at hScaleQ hCovQ hCrossQ hConstQ
  unfold quadraticHighMomentBound physicalQuadraticMomentConstant
  have hNormPos:0≤gaussianNormRealMomentConstant q (Real.sqrt (b/(N:ℝ))) (Real.sqrt b):=by
    unfold gaussianNormRealMomentConstant;positivity
  calc
    _ ≤ (4:ℝ)^q*(quadraticMomentConstant q*((4*b*L)^q*ε^q)+(L*C)^q*ε^q+
      ((2*L*D)^q*ε^q)*gaussianNormRealMomentConstant q (Real.sqrt b) (Real.sqrt b)+(L*D^2)^q*ε^q):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hScaleQ (quadraticMomentConstant_pos q).le) hCovQ)
        (mul_le_mul hCrossQ hNormC hNormPos (by positivity))) hConstQ
    _=_:=by dsimp only [ε,a];ring

end
end SlowEquilibration.GaussianQuadraticVariance
