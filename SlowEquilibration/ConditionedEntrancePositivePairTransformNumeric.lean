-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePositivePairCrossNumeric
public import Mathlib.Tactic

/-! Numerical closure of the positive source-pairing identity after the
actual defect, Fisher and absorbed-gradient estimates have been proved. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem positive_pair_transform_of_absorbed_energy
    {lam L K D C B J ε H R : ℝ}
    (hlam : 0<lam) (hB : 0≤B) (hJ : 0≤J)
    (hε : 0≤ε) (hH : 0≤H) (hR : 0≤R)
    (hIdentity : lam*L=K+lam*D-C)
    (hDefect : |D|≤10*Real.sqrt ε)
    (hCross : |C|≤Real.sqrt (J*B))
    (hFisher : J≤2*ε*lam*H)
    (hEnergy : B/lam≤2*R+ε+2*ε*H) :
    L≤K/lam+10*Real.sqrt ε+
      2*Real.sqrt (ε*H*(R+ε*(1+H))) := by
  have hDle : D≤10*Real.sqrt ε := (le_abs_self D).trans hDefect
  have hCneg : -C≤Real.sqrt (J*B) := (neg_le_abs C).trans hCross
  have hNum : lam*L≤K+lam*(10*Real.sqrt ε)+Real.sqrt (J*B) := by
    nlinarith [mul_le_mul_of_nonneg_left hDle hlam.le]
  have hRoot := positive_pair_cross_error_of_absorbed_energy hlam hB hJ
    hε hH hR hFisher hEnergy
  have hRoot' : Real.sqrt (J*B)≤
      lam*(2*Real.sqrt (ε*H*(R+ε*(1+H)))) := by
    have hh := (div_le_iff₀ hlam).mp hRoot
    nlinarith
  have hK : (K/lam)*lam=K := div_mul_cancel₀ K hlam.ne'
  nlinarith [hNum,hRoot',hK]

end SlowEquilibration.ConditionedEntrance
