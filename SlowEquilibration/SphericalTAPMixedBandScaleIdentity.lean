-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceLaplaceRatio
public import SlowEquilibration.SphericalTAPCriticalBandSectionBridge

@[expose] public section

/-! Exact deterministic `D_N` identity for a genuine nonpure source
certificate, in the ambient dimension of the mixed Palm calculation. -/

namespace SlowEquilibration.SphericalTAPMixedBandScaleIdentity
noncomputable section
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalBandSectionBridge
set_option autoImplicit false

theorem sourceMixed_bandScale_exact_identity
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (n : ℕ) (hn : 2 ≤ n) (e mN : ℝ) :
    let E := markE μ β x Q
    sourceCriticalBandScale n μ h.overlap_range β mN *
        Real.exp (β*(((n+1:ℕ):ℝ)*e-mN)) =
      (1-Q)^(-(3/2:ℝ)) *
        ((SphericalModel.latitudeNormalization n).toReal /
          Real.sqrt (((n+1:ℕ):ℝ))) *
        Real.exp (((n+1:ℕ):ℝ)*
          (CSParisiMeasure.variationalValue μ β+β*(e-E))) := by
  dsimp only
  let E := markE μ β x Q
  let s := 1-Q
  let N : ℝ := ((n+1:ℕ):ℝ)
  let r := (μ.taylorResidual h.overlap_range.1
    (sub_pos.mpr h.overlap_range.2)).xi 1
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hres : r = residualAtOne μ Q := by
    dsimp [r]
    rw [μ.taylorResidual_xi h.overlap_range.1
      (sub_pos.mpr h.overlap_range.2) 1]
    dsimp [residualAtOne]
    ring
  have hTAP := h.variational_TAP
  have hθ : CSParisiMeasure.variationalValue μ β+β*(e-E) =
      β*e+Real.log s/2+β^2*r/2 := by
    rw [hres]
    dsimp [E,s] at hTAP ⊢
    linarith [hTAP]
  have hcast : ((n-2:ℕ):ℝ) = N-3 := by
    dsimp [N]
    rw [Nat.cast_sub hn]
    push_cast
    ring
  have hpow : s^(((n-2:ℕ):ℝ)/2) =
      s^(-(3/2:ℝ))*Real.exp (N*Real.log s/2) := by
    rw [Real.rpow_def_of_pos hs,Real.rpow_def_of_pos hs,←Real.exp_add]
    congr 1
    rw [hcast]
    ring
  unfold sourceCriticalBandScale
  change Real.exp (β*mN)*
      ((SphericalModel.latitudeNormalization n).toReal /
        Real.sqrt N)*s^(((n-2:ℕ):ℝ)/2)*
      Real.exp (N*β^2*r/2)*Real.exp (β*(N*e-mN)) =
      s^(-(3/2:ℝ))*
        ((SphericalModel.latitudeNormalization n).toReal /
          Real.sqrt N)*
        Real.exp (N*(CSParisiMeasure.variationalValue μ β+β*(e-E)))
  rw [hpow,hθ]
  have hexp : Real.exp (β*mN)*Real.exp (N*β^2*r/2)*
      Real.exp (β*(N*e-mN))*Real.exp (N*Real.log s/2) =
      Real.exp (N*(β*e+Real.log s/2+β^2*r/2)) := by
    rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  calc
    _ = s^(-(3/2:ℝ))*
        ((SphericalModel.latitudeNormalization n).toReal /
          Real.sqrt N)*
        (Real.exp (β*mN)*Real.exp (N*β^2*r/2)*
          Real.exp (β*(N*e-mN))*Real.exp (N*Real.log s/2)) := by ring
    _ = _ := by rw [hexp]

end
end SlowEquilibration.SphericalTAPMixedBandScaleIdentity
