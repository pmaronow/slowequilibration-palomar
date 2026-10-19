-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapScaledContactIdentity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! Source logarithmic centering stays in the energy range required for the
raw near-pole bound, uniformly in any compact energy-shift interval. -/

namespace SlowEquilibration.SphericalPureCapCenteredEnergyBounds
noncomputable section
open Filter Set SphericalTAPCertificate TwoAtomStationarity
open SphericalPureCapSourceScalars SphericalPureCapCenteringIdentity
open PureStationarity
open scoped Topology
set_option autoImplicit false

/-- The source centered critical value is eventually nonnegative and lies
below the fixed upper-energy window, uniformly for `|t|≤L`. -/
theorem sourcePure_centered_energy_eventually_in_pole_window
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (_h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (L : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧
      ∀ t ∈ Icc (-L) L,
        0 ≤ (N:ℝ)*pureEnergyConstant p (by omega)+t-
          Real.log (N:ℝ)/(2*pureIntensityConstant p (by omega)) ∧
        (N:ℝ)*pureEnergyConstant p (by omega)+t-
          Real.log (N:ℝ)/(2*pureIntensityConstant p (by omega)) ≤
            (N:ℝ)*pureEnergyConstant p (by omega)+L := by
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  have hep : 0 < ep := pureEnergyConstant_pos p (by omega)
  have hcp : 0 < cp := pureIntensityConstant_pos p (by omega)
  have hlog : Tendsto
      (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [pow_one,one_mul,add_zero,Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.log (N:ℝ)/(N:ℝ) < cp*ep :=
    hlog.eventually (gt_mem_nhds (mul_pos hcp hep))
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2*L/ep ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 4,hsmall,hlarge] with N hN hs hl
  refine ⟨hN,?_⟩
  intro t ht
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
  have hloglt : Real.log (N:ℝ) < (N:ℝ)*(cp*ep) :=
    by simpa only [mul_comm] using (div_lt_iff₀ hNr).mp hs
  have hhalf : Real.log (N:ℝ)/(2*cp) < (N:ℝ)*ep/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*cp)).mpr
    nlinarith [hloglt]
  have hNl : L ≤ (N:ℝ)*ep/2 := by
    have hh := (div_le_iff₀ hep).mp hl
    nlinarith [hh]
  have hlogdiv0 : 0 ≤ Real.log (N:ℝ)/(2*cp) :=
    div_nonneg hlog0 (by positivity)
  constructor
  · dsimp only [ep,cp] at *
    nlinarith [ht.1]
  · dsimp only [ep,cp] at *
    linarith [ht.2]

end
end SlowEquilibration.SphericalPureCapCenteredEnergyBounds
