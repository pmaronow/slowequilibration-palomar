-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeVariance
public import SlowEquilibration.SphericalTAPLatitudeEntropyCurvature

@[expose] public section

/-! The literal one-dimensional proper-pure latitude exponent `L_p(e,a)`
used in the source Palm Laplace calculation. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeProfile
noncomputable section
open Set SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPLatitudeEntropyCurvature
open scoped Topology
set_option autoImplicit false

def sourcePureLatitudeExponent (p : ℕ) (alpha Q β e a : ℝ) : ℝ :=
  β*e*(a/Real.sqrt Q)^p+
    Real.log (1-a^2)/2+
    β^2/2*sourcePureLatitudeVariance p alpha a

def sourcePureLatitudeExponentSlope (p : ℕ) (alpha Q β e a : ℝ) : ℝ :=
  β*e*(p:ℝ)*(a/Real.sqrt Q)^(p-1)/Real.sqrt Q-
    a/(1-a^2)+
    β^2/2*sourcePureLatitudeVarianceSlope p alpha a

theorem sourcePureLatitudeExponent_hasDerivAt
    (p : ℕ) (hp : 2 ≤ p) (alpha Q β e a : ℝ)
    (hQ : 0 < Q) (ha : a ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (sourcePureLatitudeExponent p alpha Q β e)
      (sourcePureLatitudeExponentSlope p alpha Q β e a) a := by
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hs : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hm := (((hasDerivAt_id a).div_const (Real.sqrt Q)).pow p).const_mul (β*e)
  have he : HasDerivAt (fun t : ℝ => Real.log (1-t^2))
      (-2*a/(1-a^2)) a := by
    have hf : HasDerivAt (fun t : ℝ => 1-t^2) (-2*a) a := by
      convert (hasDerivAt_const a (1:ℝ)).sub ((hasDerivAt_id a).pow 2) using 1
      · funext t; simp
      · simp
    exact hf.log hs.ne'
  have hv := (sourcePureLatitudeVariance_hasDerivAt p hp alpha a).const_mul (β^2/2)
  convert (hm.add (he.div_const 2)).add hv using 1
  · rfl
  · unfold sourcePureLatitudeExponentSlope
    dsimp only [id_eq]
    field_simp
    ring

def sourcePureLatitudeExponentCurvature (p : ℕ) (alpha Q β e a : ℝ) : ℝ :=
  β*e*(p:ℝ)*((p:ℝ)-1)*(a/Real.sqrt Q)^(p-2)/(Real.sqrt Q)^2-
    (1+a^2)/(1-a^2)^2+
    β^2/2*sourcePureLatitudeVarianceCurvature p alpha a

theorem sourcePureLatitudeExponentSlope_hasDerivAt
    (p : ℕ) (hp : 2 ≤ p) (alpha Q β e a : ℝ)
    (hQ : 0 < Q) (ha : a ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (sourcePureLatitudeExponentSlope p alpha Q β e)
      (sourcePureLatitudeExponentCurvature p alpha Q β e a) a := by
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hs : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hm := (((hasDerivAt_id a).div_const (Real.sqrt Q)).pow (p-1)).const_mul
    (β*e*(p:ℝ)/Real.sqrt Q)
  have hden : HasDerivAt (fun t : ℝ => 1-t^2) (-2*a) a := by
    convert (hasDerivAt_const a (1:ℝ)).sub ((hasDerivAt_id a).pow 2) using 1
    · funext t; simp
    · simp
  have he := (hasDerivAt_id a).neg.div hden hs.ne'
  have hv := (sourcePureLatitudeVarianceSlope_hasDerivAt p hp alpha a).const_mul (β^2/2)
  convert (hm.add he).add hv using 1
  · funext t
    dsimp [sourcePureLatitudeExponentSlope]
    field_simp
    ring
  · unfold sourcePureLatitudeExponentCurvature
    have hsub : p-1-1=p-2 := by omega
    have hcast : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    simp only [id_eq,Pi.neg_apply,hsub,hcast]
    field_simp
    ring

/-- The exact ordinary second derivative of the printed pure exponent on
the whole physical interior, with no abstract Hessian hypothesis. -/
theorem sourcePureLatitudeExponent_second_deriv
    (p : ℕ) (hp : 2 ≤ p) (alpha Q β e a : ℝ)
    (hQ : 0 < Q) (ha : a ∈ Ioo (-1:ℝ) 1) :
    deriv (deriv (sourcePureLatitudeExponent p alpha Q β e)) a =
      sourcePureLatitudeExponentCurvature p alpha Q β e a := by
  have hlocal : deriv (sourcePureLatitudeExponent p alpha Q β e) =ᶠ[𝓝 a]
      sourcePureLatitudeExponentSlope p alpha Q β e := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with t ht
    exact (sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β e t hQ ht).deriv
  rw [Filter.EventuallyEq.deriv_eq hlocal]
  exact (sourcePureLatitudeExponentSlope_hasDerivAt p hp alpha Q β e a hQ ha).deriv

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeProfile
