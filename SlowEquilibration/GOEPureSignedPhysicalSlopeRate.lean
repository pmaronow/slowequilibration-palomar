-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEPurePhysicalSignedSlope
public import SlowEquilibration.GOEPhysicalCovarianceBias

/-! The sharp dimension-inverse slope estimate for the actual signed physical
GOE determinant mean. This is the analytic part of the proper-pure slope;
replacing the signed mean by the local-maximum mean is a separate step. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEPureSignedPhysicalSlopeRate
open GOEPurePhysicalSignedSlope GOEPhysicalSignedMean GOEScaling
open GOEClippedResolvent GOELogPotential JacobiPrefactors OAI.CriticalSK
set_option maxHeartbeats 500000

/-- True finite Hermite/semicircle covariance-resolvent error for the
physical Hessian dimension `n+1` and ambient dimension `n+2`. -/
theorem signed_covariance_resolvent_rate (n : ℕ) {b g k : ℝ}
    (hb : 0 < b) (hg : 0 < g)
    (hk : 2*Real.sqrt b+g ≤ k) :
    let a := scaleFactor n (n+2) b
    let s := k/a-2
    |a*jacobiNormalizedResolvent n s-b*physicalResolvent b k| ≤
      (Real.sqrt b/(g/Real.sqrt b)^3+2*b/g)/(n+1:ℝ) := by
  let a := scaleFactor n (n+2) b
  let s := k/a-2
  let j := jacobiNormalizedResolvent n s
  let m := semicircleResolvent s
  let t := g/Real.sqrt b
  have hRoot : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ht : 0 < t := div_pos hg hRoot
  have ha : 0 < a := scaleFactor_pos n (by omega) hb
  have haLe : a ≤ Real.sqrt b := scaleFactor_le_sqrt (by omega) (by omega) hb.le
  have hk0 : 0 ≤ k := by linarith
  have hDiv : k/Real.sqrt b ≤ k/a :=
    div_le_div_of_nonneg_left hk0 ha haLe
  have hEdge : 2+t ≤ k/Real.sqrt b := by
    have h := div_le_div_of_nonneg_right hk hRoot.le
    have heq : (2*Real.sqrt b+g)/Real.sqrt b=2+t := by
      dsimp only [t]
      field_simp [hRoot.ne']
    linarith
  have hs : t ≤ s := by dsimp only [s]; linarith
  have hsPos : 0 < s := ht.trans_le hs
  have hJac := normalized_resolvent_error_bound n hsPos
  have hJacAbs : |a*j-a*m| ≤ a/((n+1:ℝ)*s^3) := by
    have he : |a*j-a*m|=a*(m-j) := by
      rw [←mul_sub,abs_mul,abs_of_pos ha,abs_sub_comm,
        abs_of_nonneg hJac.1]
    rw [he]
    calc
      _ = a/(n+1:ℝ)*((n+1:ℝ)*(m-j)) := by
        field_simp
      _ ≤ a/(n+1:ℝ)*(1/s^3) :=
        mul_le_mul_of_nonneg_left hJac.2 (by positivity)
      _ = a/((n+1:ℝ)*s^3) := by
        field_simp [show (n+1:ℝ) ≠ 0 by positivity, hsPos.ne']
  have hCub : t^3 ≤ s^3 := pow_le_pow_left₀ ht.le hs 3
  have hDen : (n+1:ℝ)*t^3 ≤ (n+1:ℝ)*s^3 :=
    mul_le_mul_of_nonneg_left hCub (by positivity)
  have hJacUniform : a/((n+1:ℝ)*s^3) ≤
      Real.sqrt b/((n+1:ℝ)*t^3) := by
    calc
      _ ≤ Real.sqrt b/((n+1:ℝ)*s^3) :=
        div_le_div_of_nonneg_right haLe (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hRoot.le (by positivity) hDen
  have hBias : |a*m-b*physicalResolvent b k| ≤
      (2*b*(1:ℝ)/g)/(n+1:ℝ) := by
    simpa only [a, m, show n+1+1=n+2 by omega, Nat.cast_one, mul_one] using
      (physical_covariance_target_bias n 1 hb hg hk)
  dsimp only
  calc
    |a*j-b*physicalResolvent b k| ≤
        |a*j-a*m|+|a*m-b*physicalResolvent b k| := abs_sub_le _ _ _
    _ ≤ a/((n+1:ℝ)*s^3)+(2*b/g)/(n+1:ℝ) :=
      add_le_add hJacAbs (by simpa only [mul_one] using hBias)
    _ ≤ Real.sqrt b/((n+1:ℝ)*t^3)+(2*b/g)/(n+1:ℝ) :=
      add_le_add hJacUniform le_rfl
    _ = _ := by
      change Real.sqrt b/((n+1:ℝ)*t^3)+(2*b/g)/(n+1:ℝ) =
        (Real.sqrt b/t^3+2*b/g)/(n+1:ℝ)
      field_simp [ht.ne', show (n+1:ℝ) ≠ 0 by positivity]

/-- The signed determinant contribution to the pure energy slope differs
from the genuine semicircle slope by a fixed constant times `1/N`.
The GOE maximum restriction is handled by a separate rare-event argument. -/
theorem signed_physical_energy_slope_rate (n : ℕ) {b g k w : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hw : 0 ≤ w)
    (hk : 2*Real.sqrt b+g ≤ k) :
    let a := scaleFactor n (n+2) b
    let s := k/a-2
    |w*(n+1:ℝ)/(n+2:ℝ)/a*jacobiNormalizedResolvent n s-
        w*physicalResolvent b k| ≤
      (w/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g)/(n+1:ℝ) := by
  let a := scaleFactor n (n+2) b
  let s := k/a-2
  have ha : 0 < a := scaleFactor_pos n (by omega) hb
  have ha2 : a^2=b*(n+1:ℝ)/(n+2:ℝ) := by
    change (scaleFactor n (n+2) b)^2=b*(n+1:ℝ)/(n+2:ℝ)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (scaleFactor_square n (N:=n+2) (by omega) hb.le)
  have hcoef : ((n+1:ℝ)/(n+2:ℝ))/a=a/b := by
    apply (div_eq_div_iff ha.ne' hb.ne').mpr
    calc
      _ = b*(n+1:ℝ)/(n+2:ℝ) := by ring
      _ = a^2 := ha2.symm
      _ = a*a := by ring
  have heq : w*(n+1:ℝ)/(n+2:ℝ)/a*jacobiNormalizedResolvent n s-
      w*physicalResolvent b k =
      (w/b)*(a*jacobiNormalizedResolvent n s-b*physicalResolvent b k) := by
    calc
      _ = w*(((n+1:ℝ)/(n+2:ℝ))/a)*jacobiNormalizedResolvent n s-
          w*physicalResolvent b k := by ring
      _ = _ := by rw [hcoef]; field_simp [hb.ne']
  dsimp only
  rw [heq,abs_mul,abs_of_nonneg (div_nonneg hw hb.le)]
  exact (mul_le_mul_of_nonneg_left (signed_covariance_resolvent_rate n hb hg hk)
    (div_nonneg hw hb.le)).trans_eq (by ring)

end SlowEquilibration.GOEPureSignedPhysicalSlopeRate
