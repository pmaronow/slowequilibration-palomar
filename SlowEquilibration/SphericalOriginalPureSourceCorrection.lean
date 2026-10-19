-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalPosteriorSourceField
public import SlowEquilibration.SphericalParisiPureLatitudeCovariance

/-! The proper pure original-field correction is the literal homogeneous
value correction plus its linear tangent term. No singular score inverse
is used, and both parities are included. -/

@[expose] public section
namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm
open scoped RealInnerProductSpace

/-- Literal pure homogeneous correction with explicit observed quantities. -/
def pureRegressionCorrection {N : ℕ} (p : ℕ) (Q : ℝ) (u G : Vector N)
    (Hq e : ℝ) (x : Vector N) : ℝ :=
  ((Real.sqrt Q)^p)⁻¹*((((N : ℝ)*e-Hq)*overlap x u^p)-
    overlap x u^(p-1)*inner ℝ G x)

/-- Actual pure source correction, attached to its proper center field. -/
def pureSourceRegressionCorrection {N : ℕ} (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e : ℝ) : Vector N→ℝ :=
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  pureRegressionCorrection p Q u (surfaceGradient (field cQ J) u) (field cQ J u) e

end
end SlowEquilibration.ConditionedEntrance

namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm SphericalMarkedWindows
open SphericalPosteriorMaps SphericalParisiPureLatitudeCovariance ConditionedEntrance
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pure_rescale_power (p : ℕ) {Q : ℝ} (hQ : 0<Q) :
    Q^p=((Real.sqrt Q)^p)^2 := by
  calc
    Q^p=((Real.sqrt Q)^2)^p := congrArg (fun s : ℝ => s^p) (Real.sq_sqrt hQ.le).symm
    _=_ := by rw [←pow_mul,←pow_mul,Nat.mul_comm 2 p]

/-- True proper scalar value regression coefficient of a pure model. -/
theorem pure_original_value_coefficient (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    {Q : ℝ} (hQ : 0<Q) (r : ℝ) :
    (FiniteMixture.pure p hp c hc).xi (Real.sqrt Q*r)/
      (FiniteMixture.pure p hp c hc).xi Q=((Real.sqrt Q)^p)⁻¹*r^p := by
  have hs : (Real.sqrt Q)^p≠0 := pow_ne_zero _ (Real.sqrt_pos.mpr hQ).ne'
  rw [FiniteMixture.pure_xi,FiniteMixture.pure_xi,mul_pow,pure_rescale_power p hQ]
  field_simp [hc.ne',hs]

/-- True tangent regression coefficient of a pure model. -/
theorem pure_original_tangent_coefficient (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    {Q : ℝ} (hQ : 0<Q) (r : ℝ) :
    tangentTheta (FiniteMixture.pure p hp c hc) Q r=
      ((Real.sqrt Q)^p)⁻¹*r^(p-1) := by
  have hp' : (p : ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hs : (Real.sqrt Q)^p≠0 := pow_ne_zero _ (Real.sqrt_pos.mpr hQ).ne'
  have hsp : Real.sqrt Q*(Real.sqrt Q)^(p-1)=(Real.sqrt Q)^p := by
    rw [←pow_succ',Nat.sub_add_cancel (show 1≤p by omega)]
  have hqp : Q*Q^(p-1)=Q^p := by
    rw [←pow_succ',Nat.sub_add_cancel (show 1≤p by omega)]
  rw [tangentTheta_eq]
  unfold aScore
  rw [pure_xi1,pure_xi1,mul_pow]
  calc
    _=(c*(p : ℝ))*((Real.sqrt Q)^p)*r^(p-1)/((c*(p : ℝ))*Q^p) := by
      congr 1
      · calc
          _=c*(p : ℝ)*(Real.sqrt Q*(Real.sqrt Q)^(p-1))*r^(p-1) := by ring
          _=_ := by rw [hsp]
      · calc
          _=c*(p : ℝ)*(Q*Q^(p-1)) := by ring
          _=_ := by rw [hqp]
    _=_ := by
      rw [pure_rescale_power p hQ]
      field_simp [hc.ne',hp',hs]
    
/-- The actual proper value correction is exactly the pure homogeneous
polynomial, retaining the actual observed center value and tangent gradient. -/
theorem sourceValueRegressionCorrection_eq_pure {N : ℕ}
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) {Q : ℝ} (hQ : 0<Q)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) (e : ℝ) :
    sourceValueRegressionCorrection (FiniteMixture.pure p hp c hc) Q J u e=
      pureSourceRegressionCorrection p hp c hc Q J u e := by
  funext x
  unfold sourceValueRegressionCorrection pureSourceRegressionCorrection pureRegressionCorrection
  rw [pure_original_value_coefficient p hp c hc hQ,pure_original_tangent_coefficient p hp c hc hQ]
  ring

/-- Exact proper pure posterior original field H plus the genuine pure
source correction, at every seed and every physical value mark. -/
theorem actual_purePosterior_original_field (n : ℕ)
    (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) {Q : ℝ} (hQ : 0<Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : ℝ)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree) (x : Vector (n+1)) :
    fieldOfMixture (FiniteMixture.pure p hp c hc)
      (unpackDisorder (valuePosterior n (FiniteMixture.pure p hp c hc) Q u e g)) x=
      fieldOfMixture (FiniteMixture.pure p hp c hc) (unpackDisorder g) x+
        pureSourceRegressionCorrection p hp c hc Q (unpackDisorder g) u e x := by
  rw [actual_valuePosterior_original_field n _ hQ u hu,
    sourceValueRegressionCorrection_eq_pure p hp c hc hQ]

end
end SlowEquilibration.SphericalCriticalLatitude
