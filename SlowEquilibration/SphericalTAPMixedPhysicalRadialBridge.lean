-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceJointUpper
public import SlowEquilibration.SphericalTAPCriticalEnergyPalmAverage

@[expose] public section

/-! Exact cancellation of the common determinant/score factor in the mixed
Palm numerator and denominator. This is the printed identity (12.16),
with the source's actual all-critical radial Kac--Rice weight. -/

namespace SlowEquilibration.SphericalTAPMixedPhysicalRadialBridge
noncomputable section
open SphericalMarkedWindows SphericalTAPCriticalEnergyPalmAverage
open GOEPhysicalPotential
open SphericalSequentialRegression
open SphericalTAPMixedPhysicalChi TwoAtomStationarity
set_option autoImplicit false

theorem sourceAllCriticalRadialWeight_eq_chi_profile
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k : ℝ) :
    sourceAllCriticalRadialWeight n μ Q e k =
      sourceMixedChi n μ Q k *
      Real.exp ((n+2 : ℕ)*(Real.log (Q*μ.xi1 Q)/2-1/2)) *
      Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q e k) := by
  let a := Q*μ.xi1 Q
  let b := Q^2*μ.xi2 Q
  let N : ℝ := (n+2 : ℕ)
  let D := physicalMean n (n+2) b k
  let P := SemicirclePotential.potential (k/Real.sqrt b)
  let T := N*(Real.log (Real.sqrt b)+P)
  have ha : 0 < a := mul_pos hQ (μ.xi1_pos hQ)
  have hb : 0 < b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hT : 0 < Real.exp T := Real.exp_pos _
  have hlog : Real.log (Real.sqrt b) =
      Real.log a/2+Real.log (b/a)/2 := by
    rw [Real.log_sqrt hb.le, Real.log_div hb.ne' ha.ne']
    ring
  have hchi : sourceMixedChi n μ Q k * Real.exp T = D := by
    change (D/Real.exp T)*Real.exp T=D
    field_simp
  have hrate : -N*scoreQuadratic μ Q (scorePairEquiv (e,k))/2+T =
      N*(Real.log a/2-1/2)+N*sourceRadialProfile μ Q e k := by
    dsimp only [T,sourceRadialProfile,markedComplexity]
    rw [hlog]
    simp only [scorePairEquiv_apply,Matrix.cons_val_one]
    dsimp [P,a,b]
    ring
  unfold sourceAllCriticalRadialWeight
  change Real.exp (-N*scoreQuadratic μ Q (scorePairEquiv (e,k))/2)*D =
    sourceMixedChi n μ Q k*Real.exp (N*(Real.log a/2-1/2))*
      Real.exp (N*sourceRadialProfile μ Q e k)
  rw [← hchi]
  calc
    _ = sourceMixedChi n μ Q k *
        (Real.exp (-N*scoreQuadratic μ Q (scorePairEquiv (e,k))/2)*Real.exp T) := by ring
    _ = sourceMixedChi n μ Q k *
        Real.exp (-N*scoreQuadratic μ Q (scorePairEquiv (e,k))/2+T) := by rw [Real.exp_add]
    _ = _ := by rw [hrate,Real.exp_add]; ring

end
end SlowEquilibration.SphericalTAPMixedPhysicalRadialBridge
