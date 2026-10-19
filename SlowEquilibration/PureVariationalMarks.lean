-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSOneStepMarks
public import SlowEquilibration.PureStationarity
public import SlowEquilibration.PureResidualCoefficient
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Pure-model scalar energy marks and genuine CS variational values

The source coefficient `e_p` and its power-law marks are derived for the
actual canonical law. The value is the ordinary CS minimum. No statement
about a random ground-state or thermodynamic limit is hidden in these names.
-/

namespace SlowEquilibration.PureStationarity

noncomputable section
open Set MeasureTheory CrisantiSommers CSParisiMeasure TwoAtomStationarity PureScalarStatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def pureEnergyConstant (p : ℕ) (hp : 3 ≤ p) : ℝ :=
  ((p : ℝ)+zParameter p hp)/Real.sqrt ((p : ℝ)*(1+zParameter p hp))

theorem rpow_half_degree_sq (p : ℕ) {Q : ℝ} (hQ : 0 < Q) :
    (Real.rpow Q ((p : ℝ)/2))^2 = Q^p := by
  calc
    _ = Real.rpow (Real.rpow Q ((p : ℝ)/2)) (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = Real.rpow Q (((p : ℝ)/2)*2) := (Real.rpow_mul hQ.le _ _).symm
    _ = Q^p := by
      rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.rpow_natCast Q p

/-- Actual canonical pure scalar marks obey the source power laws and
their ordinary CS variational minimum obeys the explicit source TAP algebra. -/
theorem canonical_pure_mark_values (p : ℕ) (hp : 3 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ∃ Q ∈ Ioo (staticOverlap (zParameter p hp)) 1,
        (canonicalMinimizer (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law =
          twoAtom x Q ∧
        markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q =
          pureEnergyConstant p hp*Real.rpow Q ((p : ℝ)/2) ∧
        markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q =
          (p : ℝ)*markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q ∧
        variationalValue (FiniteMixture.pure p (by omega) 1 (by positivity)) β =
          β*pureEnergyConstant p hp*Real.rpow Q ((p : ℝ)/2)+Real.log (1-Q)/2+
            β^2*pureResidualAtOne p Q/2 := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity : (0 : ℝ) < 1)
  let z := zParameter p hp
  have hz : 0 < z := (zParameter_spec p hp).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hμxi : μ.xi = (fun r : ℝ => r^p) := by
    ext r
    exact (FiniteMixture.pure_xi p (by omega) 1 (by positivity) r).trans (one_mul _)
  have hgt : Thresholds.staticThreshold μ.xi < β := by rwa [hμxi]
  have hβpos : 0 < β := μ.staticThreshold_pos.trans hgt
  obtain ⟨x, hx, Q, hQs, hlaw, hxFormula, hroot, hcurv, hpositive⟩ := canonical_pure_parameters p hp hβ
  have hQ : Q ∈ Ioo (0 : ℝ) 1 :=
    ⟨(staticOverlap_mem_Ioo hz).1.trans hQs.1, hQs.2⟩
  have hd : 3 ≤ μ.minDegree := by rw [(CSPureModels.pure_degrees p (by omega) 1 (by positivity)).1]; exact hp
  obtain ⟨hvalue, hderiv⟩ := canonical_contacts_from_twoAtom μ hd hβpos hx hQ hlaw
  have hZ : markZ x Q = z := by
    change x*Q/(1-Q) = zParameter p hp
    rw [hxFormula]
    field_simp [hQ.1.ne', (sub_pos.mpr hQ.2).ne']
  have hpow1 : Q^(p-1)*Q = Q^p := by rw [← pow_succ]; congr 1; omega
  have hpow2 : Q^(p-2)*Q^2 = Q^p := by rw [← pow_add]; congr 1; omega
  have hA : markA μ Q = (p : ℝ)*Q^p := by
    unfold markA
    rw [pure_xi1]
    calc
      _ = (p : ℝ)*(Q^(p-1)*Q) := by ring
      _ = _ := by rw [hpow1]
  have hB : markB μ Q = (p : ℝ)*((p : ℝ)-1)*Q^p := by
    unfold markB
    rw [pure_xi2]
    calc
      _ = (p : ℝ)*((p : ℝ)-1)*(Q^(p-2)*Q^2) := by ring
      _ = _ := by rw [hpow2]
  have hY := markY_sq_from_contact μ hβpos hx hQ hvalue hderiv
  rw [hZ, hA] at hY
  have hy : 0 < markY β Q := markY_pos hβpos hQ
  let R := Real.rpow Q ((p : ℝ)/2)
  let κ := (p : ℝ)*(1+z)
  have hR : 0 < R := Real.rpow_pos_of_pos hQ.1 _
  have hκ : 0 < κ := mul_pos hpR (by linarith)
  have hR2 : R^2 = Q^p := rpow_half_degree_sq p hQ.1
  have hright2 : (Real.sqrt κ*R)^2 = κ*Q^p := by
    rw [mul_pow, Real.sq_sqrt hκ.le, hR2]
  have hYeq : markY β Q = Real.sqrt κ*R := by
    have hpos := mul_pos (Real.sqrt_pos.mpr hκ) hR
    dsimp [κ] at hright2
    nlinarith
  have hEraw : markE μ β x Q = ((p : ℝ)+z)*Q^p/markY β Q := by
    unfold markE
    rw [hA, hZ, hμxi]
    ring
  have hE : markE μ β x Q = pureEnergyConstant p hp*R := by
    rw [hEraw, hYeq, ← hR2]
    change ((p : ℝ)+z)*R^2/(Real.sqrt κ*R) = (((p : ℝ)+z)/Real.sqrt κ)*R
    field_simp [hR.ne', (Real.sqrt_pos.mpr hκ).ne']
  have hK : markK μ β Q = (p : ℝ)*markE μ β x Q := by
    unfold markK
    rw [hB, hEraw]
    field_simp [hy.ne']
    nlinarith [hY]
  have hresidual : residualAtOne μ Q = pureResidualAtOne p Q := by
    unfold residualAtOne pureResidualAtOne
    rw [hμxi, pure_xi1]
    simp only [one_pow]
    ring
  have hTAP := variationalValue_TAP μ hβpos hx hQ hlaw hvalue hderiv
  rw [hE, hresidual] at hTAP
  exact ⟨x, hx, Q, hQs, hlaw, hE, hK, by simpa only [mul_assoc] using hTAP⟩

end

end SlowEquilibration.PureStationarity
