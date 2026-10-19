-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapRawProfileIdentity

@[expose] public section

/-! Exact decomposition of the source pure cap integral into the contact
window, two compact exterior pieces, and the near-pole piece. The last piece
is kept in the original entropy-power coordinates. -/

namespace SlowEquilibration.SphericalPureCapIntegralDecomposition
noncomputable section
open Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapRawProfileIdentity PureStationarity
set_option autoImplicit false

def rawDensity (p N : ℕ) (β H t : ℝ) : ℝ :=
  (1-t^2)^(((N:ℝ)-3)/2) *
    Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)

def profileDensity (p N : ℕ) (hp : 2 ≤ p) (Q β x u t : ℝ) : ℝ :=
  sourcePureLatitudeJacobian t *
    Real.exp ((N:ℝ)*sourcePureLatitudeExponent p 1 Q β
      (markE (FiniteMixture.pure p hp 1 (by positivity)) β x Q) t+
      β*u*t^p)

theorem rawDensity_eq_profileDensity
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (N : ℕ) (u t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    rawDensity p N β ((N:ℝ)*pureEnergyConstant p (by omega)+u) t =
      profileDensity p N (by omega) Q β x u t := by
  exact sourcePure_cap_raw_profile_identity p hp h N u t ht

/-- On every closed subinterval strictly inside the positive hemisphere,
the raw source mean and the smooth profile density have equal integrals. -/
theorem raw_interval_eq_profile_interval
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (N : ℕ) (u l r : ℝ) (hl : 0 < l) (hr : r < 1)
    (hlr : l ≤ r) :
    (∫ t in l..r,
      rawDensity p N β ((N:ℝ)*pureEnergyConstant p (by omega)+u) t) =
    (∫ t in l..r, profileDensity p N (by omega) Q β x u t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  apply rawDensity_eq_profileDensity p hp h N u t
  have ht' : t ∈ Icc l r := by simpa only [uIcc_of_le hlr] using ht
  exact ⟨lt_of_lt_of_le hl ht'.1, lt_of_le_of_lt ht'.2 hr⟩

/-- The exact four-piece source partition. This identity has no asymptotic
premise and applies to the original entropy-power integrand at the pole. -/
theorem raw_cap_four_piece
    (p N : ℕ) (hN : 4 ≤ N) (β H a q b ε : ℝ) :
    (∫ t in a..1, rawDensity p N β H t) =
      (∫ t in a..q-b, rawDensity p N β H t) +
      (∫ t in q-b..q+b, rawDensity p N β H t) +
      (∫ t in q+b..1-ε, rawDensity p N β H t) +
      (∫ t in 1-ε..1, rawDensity p N β H t) := by
  have hpow : 0 ≤ ((N:ℝ)-3)/2 := by
    have : (4:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpowCont : Continuous (fun t : ℝ => (1-t^2)^(((N:ℝ)-3)/2)) :=
    (Real.continuous_rpow_const hpow).comp
      (continuous_const.sub (continuous_id.pow 2))
  have hresCont : Continuous (pureResidualCoefficient p β) := by
    unfold pureResidualCoefficient pureResidualAtOne
    fun_prop
  have hf : Continuous (rawDensity p N β H) := by
    unfold rawDensity
    exact hpowCont.mul (Real.continuous_exp.comp (by fun_prop))
  have hi (l r : ℝ) : IntervalIntegrable (rawDensity p N β H) volume l r :=
    hf.intervalIntegrable l r
  calc
    _ = (∫ t in a..1-ε, rawDensity p N β H t) +
        (∫ t in 1-ε..1, rawDensity p N β H t) :=
          (intervalIntegral.integral_add_adjacent_intervals (hi a (1-ε)) (hi (1-ε) 1)).symm
    _ = ((∫ t in a..q+b, rawDensity p N β H t) +
        (∫ t in q+b..1-ε, rawDensity p N β H t)) +
        (∫ t in 1-ε..1, rawDensity p N β H t) := by
          rw [intervalIntegral.integral_add_adjacent_intervals (hi a (q+b)) (hi (q+b) (1-ε))]
    _ = _ := by
          rw [intervalIntegral.integral_add_adjacent_intervals (hi a (q-b)) (hi (q-b) (q+b))]

/-- Exact source decomposition with the three compact pieces already in
the profile coordinates used by the local Gaussian and exterior estimates. -/
theorem sourcePure_cap_profile_and_pole
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (N : ℕ) (hN : 4 ≤ N) (u a b ε : ℝ)
    (ha : 0 < a) (hab : a ≤ Real.sqrt Q-b)
    (hb : 0 ≤ b) (hqε : Real.sqrt Q+b ≤ 1-ε)
    (hε : 0 < ε) :
    (∫ t in a..1,
      rawDensity p N β ((N:ℝ)*pureEnergyConstant p (by omega)+u) t) =
      (∫ t in a..Real.sqrt Q-b, profileDensity p N (by omega) Q β x u t) +
      (∫ t in Real.sqrt Q-b..Real.sqrt Q+b,
        profileDensity p N (by omega) Q β x u t) +
      (∫ t in Real.sqrt Q+b..1-ε, profileDensity p N (by omega) Q β x u t) +
      (∫ t in 1-ε..1,
        rawDensity p N β ((N:ℝ)*pureEnergyConstant p (by omega)+u) t) := by
  rw [raw_cap_four_piece p N hN β
    ((N:ℝ)*pureEnergyConstant p (by omega)+u) a (Real.sqrt Q) b ε]
  have hq0 : 0 < Real.sqrt Q-b := lt_of_lt_of_le ha hab
  have hqr : Real.sqrt Q+b < 1 := lt_of_le_of_lt hqε (by linarith)
  have hε1 : 1-ε < 1 := by linarith
  rw [raw_interval_eq_profile_interval p hp h N u a (Real.sqrt Q-b)
      ha (by linarith : Real.sqrt Q-b < 1) (by linarith),
    raw_interval_eq_profile_interval p hp h N u (Real.sqrt Q-b)
      (Real.sqrt Q+b) hq0 hqr (by linarith),
    raw_interval_eq_profile_interval p hp h N u (Real.sqrt Q+b)
      (1-ε) (by linarith) hε1 hqε]

end
end SlowEquilibration.SphericalPureCapIntegralDecomposition
