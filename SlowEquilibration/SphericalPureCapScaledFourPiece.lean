-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapCenteredEnergyBounds

@[expose] public section

/-! Exact, finite-dimensional four-piece identity for the source pure
annealed cap at its logarithmically centered critical value. -/

namespace SlowEquilibration.SphericalPureCapScaledFourPiece
noncomputable section
open Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapSourceScalars SphericalPureCapTailScale
open SphericalPureCapIntegralDecomposition
open SphericalPureCapScaledContactIdentity PureStationarity
open SphericalModel
set_option autoImplicit false

/-- At each physical dimension, the scaled raw cap integral is exactly the
sum of the two scaled compact tails, the centered contact integral, and the
scaled raw near-pole integral. -/
theorem sourcePure_scaled_cap_four_piece
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (N : ℕ) (hN : 4 ≤ N) (t a b ε : ℝ)
    (ha : 0 < a) (hab : a ≤ Real.sqrt Q-b)
    (hb : 0 ≤ b) (hqε : Real.sqrt Q+b ≤ 1-ε)
    (hε : 0 < ε) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let φ := sourcePureLatitudeExponent p 1 Q β (markE μ β x Q)
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    let F := CSParisiMeasure.variationalValue μ β
    let u := t-Real.log (N:ℝ)/(2*cp)
    capScale N F (1/(2*x)) *
      ((latitudeNormalization (N-1)).toReal *
        (∫ z in a..1, rawDensity p N β ((N:ℝ)*ep+u) z)) =
    capScale N F (1/(2*x)) *
      ((latitudeNormalization (N-1)).toReal *
        (∫ z in a..q-b, profileDensity p N (by omega) Q β x u z)) +
    (latitudeNormalization (N-1)).toReal *
      (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
        Real.exp ((N:ℝ)*(φ z-φ q)+β*t*q^p+
          β*u*(z^p-q^p))) +
    capScale N F (1/(2*x)) *
      ((latitudeNormalization (N-1)).toReal *
        (∫ z in q+b..1-ε, profileDensity p N (by omega) Q β x u z)) +
    capScale N F (1/(2*x)) *
      ((latitudeNormalization (N-1)).toReal *
        (∫ z in 1-ε..1, rawDensity p N β ((N:ℝ)*ep+u) z)) := by
  dsimp only
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let u := t-Real.log (N:ℝ)/(2*cp)
  let F := CSParisiMeasure.variationalValue
    (FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)) β
  let φ := sourcePureLatitudeExponent p 1 Q β
    (markE (FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)) β x Q)
  have hsplit := sourcePure_cap_profile_and_pole p hp h N hN u a b ε
    ha hab hb hqε hε
  have hlocal := sourcePure_scaled_profile_interval_eq_centered
    p hp h N (by omega : 0 < N) t (q-b) (q+b)
  have hlocal' :
      capScale N F (1/(2*x)) *
        ((latitudeNormalization (N-1)).toReal *
          (∫ z in q-b..q+b, profileDensity p N (by omega) Q β x u z)) =
        (latitudeNormalization (N-1)).toReal *
          (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
            Real.exp ((N:ℝ)*(φ z-φ q)+β*t*q^p+β*u*(z^p-q^p))) := by
    simpa only [profileDensity,q,φ,cp,u,F] using hlocal
  rw [hsplit]
  calc
    capScale N F (1/(2*x)) *
        ((latitudeNormalization (N-1)).toReal *
          ((∫ z in a..q-b, profileDensity p N (by omega) Q β x u z) +
           (∫ z in q-b..q+b, profileDensity p N (by omega) Q β x u z) +
           (∫ z in q+b..1-ε, profileDensity p N (by omega) Q β x u z) +
           (∫ z in 1-ε..1, rawDensity p N β
             ((N:ℝ)*pureEnergyConstant p (by omega)+u) z))) =
      capScale N F (1/(2*x)) *
        ((latitudeNormalization (N-1)).toReal *
          (∫ z in a..q-b, profileDensity p N (by omega) Q β x u z)) +
      capScale N F (1/(2*x)) *
        ((latitudeNormalization (N-1)).toReal *
          (∫ z in q-b..q+b, profileDensity p N (by omega) Q β x u z)) +
      capScale N F (1/(2*x)) *
        ((latitudeNormalization (N-1)).toReal *
          (∫ z in q+b..1-ε, profileDensity p N (by omega) Q β x u z)) +
      capScale N F (1/(2*x)) *
        ((latitudeNormalization (N-1)).toReal *
          (∫ z in 1-ε..1, rawDensity p N β
            ((N:ℝ)*pureEnergyConstant p (by omega)+u) z)) := by ring
    _ = _ := by rw [hlocal']

end
end SlowEquilibration.SphericalPureCapScaledFourPiece
