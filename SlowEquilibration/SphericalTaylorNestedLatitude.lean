-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorBandPartition
public import SlowEquilibration.SphericalLatitudeLaplace

@[expose] public section

/-! The genuine transverse Taylor band is a pair of nested latitude
sections. Its two entropy factors multiply to precisely 1-Q. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def bandOuterLatitude (Q q : ℝ) : ℝ := Real.sqrt Q*q

def bandInnerLatitude (Q q : ℝ) : ℝ := Real.sqrt (Q*(1-q^2)/(1-Q*q^2))

theorem band_latitude_denominator_pos {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1)
    (hq : |q|<1) : 0<1-Q*q^2 := by
  have hsq : q^2<1 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
  have hm := mul_lt_mul_of_pos_left hsq hQ.1
  linarith [hQ.2]

theorem bandOuterLatitude_sq {Q q : ℝ} (hQ : 0≤Q) :
    (bandOuterLatitude Q q)^2=Q*q^2 := by
  rw [bandOuterLatitude,mul_pow,Real.sq_sqrt hQ]

theorem bandInnerLatitude_sq {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1)
    (hq : |q|<1) : (bandInnerLatitude Q q)^2=Q*(1-q^2)/(1-Q*q^2) := by
  have hsq : 0<1-q^2 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
  exact Real.sq_sqrt (div_nonneg (mul_nonneg hQ.1.le hsq.le)
    (band_latitude_denominator_pos hQ hq).le)

theorem bandOuterLatitude_abs_lt {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1)
    (hq : |q|<1) : |bandOuterLatitude Q q|<1 := by
  have hs := bandOuterLatitude_sq (q := q) hQ.1.le
  have hd := band_latitude_denominator_pos hQ hq
  apply abs_lt.mpr
  constructor <;> nlinarith [sq_nonneg (bandOuterLatitude Q q+1),sq_nonneg (bandOuterLatitude Q q-1)]

theorem bandInnerLatitude_mem {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1)
    (hq : |q|<1) : bandInnerLatitude Q q∈Ioo (0 : ℝ) 1 := by
  have hd := band_latitude_denominator_pos hQ hq
  have hsq : 0<1-q^2 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
  have ht : 0<bandInnerLatitude Q q := Real.sqrt_pos.mpr (div_pos (mul_pos hQ.1 hsq) hd)
  refine ⟨ht,?_⟩
  have hs := bandInnerLatitude_sq hQ hq
  have hl : Q*(1-q^2)/(1-Q*q^2)<1 := (div_lt_one hd).mpr (by linarith [hQ.2])
  nlinarith

theorem band_latitude_entropy_product {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1)
    (hq : |q|<1) :
    (1-(bandOuterLatitude Q q)^2)*(1-(bandInnerLatitude Q q)^2)=1-Q := by
  rw [bandOuterLatitude_sq hQ.1.le,bandInnerLatitude_sq hQ hq]
  field_simp [(band_latitude_denominator_pos hQ hq).ne']
  ring

theorem band_latitude_entropy_log {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1)
    (hq : |q|<1) :
    Real.log (1-(bandOuterLatitude Q q)^2)+Real.log (1-(bandInnerLatitude Q q)^2)=
      Real.log (1-Q) := by
  have hr := bandOuterLatitude_abs_lt hQ hq
  have ht := bandInnerLatitude_mem hQ hq
  have hrp : 0<1-(bandOuterLatitude Q q)^2 := by nlinarith [(abs_lt.mp hr).1,(abs_lt.mp hr).2]
  have htp : 0<1-(bandInnerLatitude Q q)^2 := by nlinarith [ht.1,ht.2]
  rw [← Real.log_mul hrp.ne' htp.ne',band_latitude_entropy_product hQ hq]

theorem transverseBandPoint_eq_nestedLatitude {n : ℕ} (hn : 1≤n)
    {Q q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1) (hq : |q|<1)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (y : Vector (n+1)) (z : Vector n) :
    transverseBandPoint (latitudeMap w e q y) (bottomTransverseFrame e y) Q z=
      latitudeMap w e (bandOuterLatitude Q q)
        (latitudeMap y (latitudeFrameAt y) (bandInnerLatitude Q q) z) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnp : (0 : ℝ)<((n+1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ)<((n+2 : ℕ) : ℝ) := by positivity
  have hd := band_latitude_denominator_pos hQ hq
  have hQsub : 0<1-Q := sub_pos.mpr hQ.2
  have hqs : 0<1-q^2 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
  have hts := bandInnerLatitude_sq hQ hq
  have htp := bandInnerLatitude_mem hQ hq
  have htarg : 0<1-(bandInnerLatitude Q q)^2 := by nlinarith [htp.1,htp.2]
  have hcoeffY : Real.sqrt Q*Real.sqrt (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*(1-q^2))=
      Real.sqrt (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*(1-(bandOuterLatitude Q q)^2))*bandInnerLatitude Q q := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) htp.1.le)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt hQ.1.le,Real.sq_sqrt (by positivity),
      bandOuterLatitude_sq hQ.1.le,Real.sq_sqrt (by positivity),hts]
    field_simp [hd.ne']
  have hcoeffZ : Real.sqrt Q*Real.sqrt (((n+2 : ℕ) : ℝ)*(1-Q)/(Q*(n : ℝ)))=
      Real.sqrt (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*(1-(bandOuterLatitude Q q)^2))*
        Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-(bandInnerLatitude Q q)^2)) := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt hQ.1.le,
      Real.sq_sqrt (div_nonneg (mul_nonneg hN.le hQsub.le) (mul_nonneg hQ.1.le hn0.le)),
      bandOuterLatitude_sq hQ.1.le,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),hts]
    field_simp [hQ.1.ne',hn0.ne',hnp.ne',hd.ne']
    ring
  simp only [transverseBandPoint,latitudeMap,transverseOffset,bottomTransverseFrame,
    map_add,map_smul,smul_add,smul_smul]
  rw [hcoeffY,hcoeffZ]
  simp only [bandOuterLatitude,LinearIsometry.coe_comp,Function.comp_apply,Nat.add_assoc,Nat.reduceAdd]
  abel

end
end SlowEquilibration.SphericalTaylorRemainder
