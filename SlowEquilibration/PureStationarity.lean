-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.TwoAtomStationarity
public import SlowEquilibration.MixtureElasticity

@[expose] public section

namespace SlowEquilibration.TwoAtomStationarity

noncomputable section
open Set CrisantiSommers PureScalarStatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The true scalar stationarity equation of any genuine positive two-atom
contact. The actual entropy identities eliminate the inverse temperature. -/
theorem contact_upsilon_equation (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hvalue : CSStructure.potential μ β (twoAtom x Q) Q = 0)
    (hderiv : deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0) :
    upsilon (x*Q/(1-Q)) = μ.xi Q/(Q*μ.xi1 Q) := by
  obtain ⟨hslope, hval⟩ := contact_equations μ β hx hQ hvalue hderiv
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hQden : 1-Q ≠ 0 := (sub_pos.mpr hQ.2).ne'
  have hβsq : β^2 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hslope
    have hpos : 0 < Q/(C*(1-Q)) := div_pos hQ.1 (mul_pos hC (sub_pos.mpr hQ.2))
    linarith
  have hxi : μ.xi Q = ((Real.log (C/(1-Q))-x*Q/C)/x^2)/β^2 := by
    apply (eq_div_iff hβsq).mpr
    nlinarith [hval]
  have hxi1 : μ.xi1 Q = (Q/(C*(1-Q)))/β^2 := by
    apply (eq_div_iff hβsq).mpr
    nlinarith [hslope]
  have hβne : β ≠ 0 := by
    intro heq
    rw [heq] at hβsq
    norm_num at hβsq
  have hz : 0 < x*Q/(1-Q) := div_pos (mul_pos hx.1 hQ.1) (sub_pos.mpr hQ.2)
  have hsum : 1+x*Q/(1-Q) = C/(1-Q) := by
    dsimp [C, profileConstant]
    field_simp [hQden]
  rw [upsilon_eq hz, hsum, hxi, hxi1]
  field_simp [hβne, hC.ne', hx.1.ne', hQ.1.ne', hQden]

end

end SlowEquilibration.TwoAtomStationarity

namespace SlowEquilibration.PureStationarity

noncomputable section
open Set MeasureTheory CrisantiSommers PureScalarStatic TwoAtomStationarity CSParisiMeasure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem pure_xi1 (p : ℕ) (hp : 2 ≤ p) (r : ℝ) :
    (FiniteMixture.pure p hp 1 (by positivity)).xi1 r = (p : ℝ)*r^(p-1) := by
  unfold FiniteMixture.xi1
  rw [CSPureModels.pure_support]
  simp [FiniteMixture.pure]

theorem pure_xi2 (p : ℕ) (hp : 2 ≤ p) (r : ℝ) :
    (FiniteMixture.pure p hp 1 (by positivity)).xi2 r =
      (p : ℝ)*((p : ℝ)-1)*r^(p-2) := by
  unfold FiniteMixture.xi2
  rw [CSPureModels.pure_support]
  simp only [Finset.sum_singleton, FiniteMixture.curvatureCoeff, FiniteMixture.pure,
    Finsupp.single_eq_same, one_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  norm_num

/-- Pure two-atom contact stationarity identifies its actual scalar
parameter with the uniquely constructed ordinary integral root. -/
theorem pure_contact_z_eq (p : ℕ) (hp : 3 ≤ p) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hvalue : CSStructure.potential (FiniteMixture.pure p (by omega) 1 (by positivity))
      β (twoAtom x Q) Q = 0)
    (hderiv : deriv (CSStructure.potential (FiniteMixture.pure p (by omega) 1 (by positivity))
      β (twoAtom x Q)) Q = 0) :
    x*Q/(1-Q) = zParameter p hp := by
  have h := contact_upsilon_equation (FiniteMixture.pure p (by omega) 1 (by positivity))
    β hx hQ hvalue hderiv
  have hpow : Q^p = Q^(p-1)*Q := by rw [← pow_succ]; congr 1; omega
  rw [FiniteMixture.pure_xi, one_mul, pure_xi1, hpow] at h
  have hratio : Q^(p-1)*Q/(Q*((p : ℝ)*Q^(p-1))) = 1/(p : ℝ) := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    field_simp [hpR, hQ.1.ne', pow_ne_zero (p-1) hQ.1.ne']
  rw [hratio] at h
  have hz : 0 < x*Q/(1-Q) := div_pos (mul_pos hx.1 hQ.1) (sub_pos.mpr hQ.2)
  exact strictAntiOn_upsilon.injOn hz.le (zParameter_spec p hp).1.le
    (h.trans (zParameter_spec p hp).2.symm)

/-- The actual canonical pure-model minimizer has the manuscript's explicit
parameters and ordinary contact curvature. All contact equations are derived
from the actual canonical minimizer, rather than supplied as premises. -/
theorem canonical_pure_parameters (p : ℕ) (hp : 3 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ∃ Q ∈ Ioo (staticOverlap (zParameter p hp)) 1,
        (canonicalMinimizer (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law =
          twoAtom x Q ∧
        x = zParameter p hp*(1-Q)/Q ∧
        β^2*(p : ℝ)*(1+zParameter p hp)*Q^(p-2)*(1-Q)^2 = 1 ∧
        deriv (deriv (CSStructure.potential
          (FiniteMixture.pure p (by omega) 1 (by positivity)) β
          (canonicalMinimizer (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law)) Q =
            (1/(1-Q)^2)*(1-((p : ℝ)-1)/(1+zParameter p hp)) ∧
        0 < deriv (deriv (CSStructure.potential
          (FiniteMixture.pure p (by omega) 1 (by positivity)) β
          (canonicalMinimizer (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law)) Q := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity : (0 : ℝ) < 1)
  have hμxi : μ.xi = (fun r : ℝ => r^p) := by
    ext r
    exact (FiniteMixture.pure_xi p (by omega) 1 (by positivity) r).trans (one_mul _)
  have hgt : Thresholds.staticThreshold μ.xi < β := by rwa [hμxi]
  obtain ⟨x, hx, Q, hQ, hlaw, hrest⟩ :=
    CSPureModels.pure_canonicalMinimizer_strict_oneStep p hp 1 (by positivity) hgt
  have hvalue : CSStructure.potential μ β (twoAtom x Q) Q = 0 := by
    rw [← hlaw]
    exact hrest.1
  have hderiv : deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0 := by
    rw [← hlaw]
    exact hrest.2.1
  have hzEq := pure_contact_z_eq p hp β hx hQ hvalue hderiv
  let z := zParameter p hp
  have hz : 0 < z := (zParameter_spec p hp).1
  have hzCross : x*Q = z*(1-Q) := (div_eq_iff (sub_pos.mpr hQ.2).ne').mp hzEq
  have hxFormula : x = z*(1-Q)/Q := (eq_div_iff hQ.1.ne').mpr hzCross
  have hQabove : staticOverlap z < Q := by
    apply (div_lt_iff₀ (by linarith : 0 < 1+z)).mpr
    have h := mul_lt_mul_of_pos_right hx.2 hQ.1
    rw [hzCross] at h
    nlinarith
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hCeq : C = (1-Q)*(1+z) := by
    dsimp [C, profileConstant]
    rw [hzCross]
    ring
  have hslope := (contact_equations μ β hx hQ hvalue hderiv).1
  rw [pure_xi1] at hslope
  have hpow : Q^(p-1) = Q^(p-2)*Q := by rw [← pow_succ]; congr 1; omega
  have hcross := (eq_div_iff (mul_ne_zero hC.ne' (sub_pos.mpr hQ.2).ne')).mp hslope
  have hroot : β^2*(p : ℝ)*(1+z)*Q^(p-2)*(1-Q)^2 = 1 := by
    apply mul_left_cancel₀ hQ.1.ne'
    calc
      Q*(β^2*(p : ℝ)*(1+z)*Q^(p-2)*(1-Q)^2) =
          (β^2*((p : ℝ)*Q^(p-1)))*(C*(1-Q)) := by rw [hpow, hCeq]; ring
      _ = Q := hcross
      _ = Q*1 := by ring
  have hβcore : β^2*(p : ℝ)*Q^(p-2) = 1/((1+z)*(1-Q)^2) := by
    apply (eq_div_iff (mul_ne_zero (by linarith : 1+z ≠ 0)
      (pow_ne_zero 2 (sub_pos.mpr hQ.2).ne'))).mpr
    calc
      (β^2*(p : ℝ)*Q^(p-2))*((1+z)*(1-Q)^2) =
          β^2*(p : ℝ)*(1+z)*Q^(p-2)*(1-Q)^2 := by ring
      _ = 1 := hroot
  have hprofile : xHat (canonicalMinimizer μ β).law Q = 1-Q := by
    rw [hlaw, xHat_twoAtom ⟨hx.1.le, hx.2.le⟩ hQ.1.le, ite_eq_left le_rfl]
    ring
  have hxi2 : μ.xi2 Q = (p : ℝ)*((p : ℝ)-1)*Q^(p-2) := pure_xi2 p (by omega) Q
  have hcurv := (CSStructure.potential_deriv_hasDerivAt μ β (canonicalMinimizer μ β).law
    (canonicalMinimizer μ β).hasCutoff hQ.2).deriv
  rw [hprofile, hxi2] at hcurv
  have hcurvEq : deriv (deriv (CSStructure.potential μ β (canonicalMinimizer μ β).law)) Q =
      (1/(1-Q)^2)*(1-((p : ℝ)-1)/(1+z)) := by
    calc
      _ = 1/(1-Q)^2-β^2*((p : ℝ)*((p : ℝ)-1)*Q^(p-2)) := hcurv
      _ = 1/(1-Q)^2-((p : ℝ)-1)*(β^2*(p : ℝ)*Q^(p-2)) := by ring
      _ = _ := by
        rw [hβcore]
        field_simp [(sub_pos.mpr hQ.2).ne', show 1+z ≠ 0 by linarith]
  exact ⟨x, hx, Q, ⟨hQabove, hQ.2⟩, hlaw, hxFormula, hroot, hcurvEq, hrest.2.2.1⟩

end

end SlowEquilibration.PureStationarity
