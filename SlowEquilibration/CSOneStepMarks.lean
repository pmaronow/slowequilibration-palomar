-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSCanonicalOneStepValue
public import SlowEquilibration.MixtureElasticity

@[expose] public section

/-!
# Actual one-step scalar marks and variational TAP algebra

These are literal scalar expressions from the actual covariance and law.
The identities and strict edge margin are derived from actual contact
calculus. The value is the ordinary CS variational minimum, with no
assumption identifying these scalars with stochastic thermodynamic limits.
-/

namespace SlowEquilibration.TwoAtomStationarity

noncomputable section
open Set MeasureTheory CrisantiSommers CSParisiMeasure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def markZ (x Q : ℝ) : ℝ := x*Q/(1-Q)
def markY (β Q : ℝ) : ℝ := Q/(β*(1-Q))
def markA (μ : FiniteMixture) (Q : ℝ) : ℝ := Q*μ.xi1 Q
def markB (μ : FiniteMixture) (Q : ℝ) : ℝ := Q^2*μ.xi2 Q
def markE (μ : FiniteMixture) (β x Q : ℝ) : ℝ :=
  (markA μ Q+markZ x Q*μ.xi Q)/markY β Q
def markK (μ : FiniteMixture) (β Q : ℝ) : ℝ := markY β Q+markB μ Q/markY β Q
def residualAtOne (μ : FiniteMixture) (Q : ℝ) : ℝ := μ.xi 1-μ.xi Q-(1-Q)*μ.xi1 Q

theorem markY_pos {β Q : ℝ} (hβ : 0 < β) (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    0 < markY β Q := div_pos hQ.1 (mul_pos hβ (sub_pos.mpr hQ.2))

theorem markB_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) : 0 < markB μ Q :=
  mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)

theorem markE_beta (μ : FiniteMixture) {β x Q : ℝ} (hβ : 0 < β)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    β*markE μ β x Q = β^2*((1-Q)*μ.xi1 Q+x*μ.xi Q) := by
  unfold markE markA markZ markY
  field_simp [hβ.ne', hQ.1.ne', (sub_pos.mpr hQ.2).ne']

theorem markB_div_markY_sq (μ : FiniteMixture) {β Q : ℝ} (hβ : 0 < β)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    markB μ Q/(markY β Q)^2 = β^2*(1-Q)^2*μ.xi2 Q := by
  unfold markB markY
  field_simp [hβ.ne', hQ.1.ne', (sub_pos.mpr hQ.2).ne']

theorem markZ_div_markY {β x Q : ℝ} (hβ : 0 < β) (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    markZ x Q/markY β Q = β*x := by
  unfold markZ markY
  field_simp [hβ.ne', hQ.1.ne', (sub_pos.mpr hQ.2).ne']

/-- The actual contact slope determines the exact squared scale mark. -/
theorem markY_sq_from_contact (μ : FiniteMixture) {β x Q : ℝ} (hβ : 0 < β)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hvalue : CSStructure.potential μ β (twoAtom x Q) Q = 0)
    (hderiv : deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0) :
    (markY β Q)^2 = (1+markZ x Q)*markA μ Q := by
  have hslope := (contact_equations μ β hx hQ hvalue hderiv).1
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hxi1 : μ.xi1 Q = (Q/(C*(1-Q)))/β^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hβ.ne')).mpr
    nlinarith [hslope]
  unfold markY markZ markA
  rw [hxi1]
  field_simp [hβ.ne', hQ.1.ne', hC.ne', (sub_pos.mpr hQ.2).ne']
  dsimp [C, profileConstant]
  ring

/-- Genuine nondegenerate contact curvature implies the actual strict
scalar Hessian edge margin and its exact square formula. -/
theorem markK_edge_from_contact (μ : FiniteMixture) {β x Q : ℝ} (hβ : 0 < β)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hcurv : 0 < deriv (deriv (CSStructure.potential μ β (twoAtom x Q))) Q) :
    markB μ Q/(markY β Q)^2 < 1 ∧
      markK μ β Q-2*Real.sqrt (markB μ Q) =
        (markY β Q-Real.sqrt (markB μ Q))^2/markY β Q ∧
      0 < markK μ β Q-2*Real.sqrt (markB μ Q) := by
  have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability ⟨hx.1.le, hx.2.le⟩
  have hcut := twoAtom_hasCutoff (x := x) ⟨hQ.1.le, hQ.2⟩
  have hprofile : xHat (twoAtom x Q) Q = 1-Q := by
    rw [xHat_twoAtom ⟨hx.1.le, hx.2.le⟩ hQ.1.le, ite_eq_left le_rfl]
    ring
  rw [(CSStructure.potential_deriv_hasDerivAt μ β (twoAtom x Q) hcut hQ.2).deriv,
    hprofile] at hcurv
  have hs : 0 < (1-Q)^2 := sq_pos_of_pos (sub_pos.mpr hQ.2)
  have hratio : β^2*(1-Q)^2*μ.xi2 Q < 1 := by
    have hlt : β^2*μ.xi2 Q < 1/(1-Q)^2 := by linarith
    have hh := (lt_div_iff₀ hs).mp hlt
    nlinarith
  have hfrac : markB μ Q/(markY β Q)^2 < 1 := by
    rw [markB_div_markY_sq μ hβ hQ]
    exact hratio
  have hy := markY_pos hβ hQ
  have hb := markB_pos μ hQ.1
  have hyb : markB μ Q < (markY β Q)^2 := (div_lt_one (sq_pos_of_pos hy)).mp hfrac
  have hsqrt : Real.sqrt (markB μ Q) < markY β Q := by
    nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg (markB μ Q)]
  have hEq : markK μ β Q-2*Real.sqrt (markB μ Q) =
      (markY β Q-Real.sqrt (markB μ Q))^2/markY β Q := by
    unfold markK
    field_simp [hy.ne']
    nlinarith [Real.sq_sqrt hb.le]
  refine ⟨hfrac, hEq, ?_⟩
  rw [hEq]
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hsqrt)) hy

/-- Actual variational TAP identity: the ordinary CS minimum is expressed
through the literal scalar mark and residual covariance. Its hypotheses are
true law/contact data, with no free-energy or energy formula assumed. -/
theorem variationalValue_TAP (μ : FiniteMixture) {β x Q : ℝ} (hβ : 0 < β)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hlaw : (canonicalMinimizer μ β).law = twoAtom x Q)
    (hvalue : CSStructure.potential μ β (twoAtom x Q) Q = 0)
    (hderiv : deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0) :
    variationalValue μ β = β*markE μ β x Q+Real.log (1-Q)/2+
      β^2*residualAtOne μ Q/2 := by
  obtain ⟨hslope, hval⟩ := contact_equations μ β hx hQ hvalue hderiv
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hscaled : β^2*(1-Q)*μ.xi1 Q = Q/C := by
    calc
      _ = (1-Q)*(β^2*μ.xi1 Q) := by ring
      _ = (1-Q)*(Q/(C*(1-Q))) := by rw [hslope]
      _ = _ := by field_simp [hC.ne', (sub_pos.mpr hQ.2).ne']
  have hlog : Real.log (C/(1-Q))/x = β^2*x*μ.xi Q+β^2*(1-Q)*μ.xi1 Q := by
    apply (div_eq_iff hx.1.ne').mpr
    have hv := (eq_div_iff (pow_ne_zero 2 hx.1.ne')).mp hval
    calc
      Real.log (C/(1-Q)) = (β^2*μ.xi Q)*x^2+x*(Q/C) := by
        change (β^2*μ.xi Q)*x^2 = Real.log (C/(1-Q))-x*Q/C at hv
        rw [mul_div_assoc] at hv
        linarith
      _ = _ := by rw [← hscaled]; ring
  rw [variationalValue_of_twoAtom μ β hx hQ hlaw, hlog, markE_beta μ hβ hQ]
  unfold residualAtOne
  ring

/-- A literal positive two-atom canonical law has genuine contact value
and derivative zero. Both follow from actual necessary optimality and the
derived origin contact, without a contact or stationarity premise. -/
theorem canonical_contacts_from_twoAtom (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β x Q : ℝ} (hβ : 0 < β) (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hlaw : (canonicalMinimizer μ β).law = twoAtom x Q) :
    CSStructure.potential μ β (twoAtom x Q) Q = 0 ∧
      deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0 := by
  have hmax := CSStructure.minimizer_firstVariation_maximum_zero μ hd hβ
    (canonicalMinimizer μ β) (canonicalMinimizer_isMinimizer μ β)
  have hs := hmax.2.1
  rw [hlaw, twoAtom, ae_add_measure_iff] at hs
  have hn : ENNReal.ofReal (1-x) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hx.2))
  have hQzero : firstVariation β μ.xi (twoAtom x Q) Q = 0 := by
    have hh := (Measure.ae_ennreal_smul_measure_iff hn).mp hs.2
    simpa [twoAtom] using hh
  have hVzero : CSStructure.potential μ β (twoAtom x Q) Q = 0 := by
    unfold CSStructure.potential
    rw [hQzero]
    norm_num
  have hnonneg := CSStructure.potential_nonneg_of_minimizer μ hd hβ
    (canonicalMinimizer μ β) (canonicalMinimizer_isMinimizer μ β)
  rw [hlaw] at hnonneg
  exact ⟨hVzero, ContactGeometry.contact_deriv_zero hnonneg hQ hVzero⟩

/-- Actual canonical one-step marks and the variational TAP identity under
the proved curvature class. Every law and contact equation is obtained from
genuine canonical minimization; no stationarity or edge premise is imposed. -/
theorem canonical_oneStep_marks_of_curvature (μ : FiniteMixture)
    (hd : 3 ≤ μ.minDegree) {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc (0 : ℝ) 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∃ Q ∈ Ioo (0 : ℝ) 1,
      (canonicalMinimizer μ β).law = twoAtom x Q ∧
      (markY β Q)^2 = (1+markZ x Q)*markA μ Q ∧
      markZ x Q/markY β Q = β*x ∧ markZ x Q/markY β Q < β ∧
      markB μ Q/(markY β Q)^2 < 1 ∧
      markK μ β Q-2*Real.sqrt (markB μ Q) =
        (markY β Q-Real.sqrt (markB μ Q))^2/markY β Q ∧
      0 < markK μ β Q-2*Real.sqrt (markB μ Q) ∧
      variationalValue μ β = β*markE μ β x Q+Real.log (1-Q)/2+
        β^2*residualAtOne μ Q/2 := by
  obtain ⟨x, hx, Q, hQ, hlaw, hrest⟩ := canonicalMinimizer_strict_oneStep μ hd hgt hξ
  have hβ : 0 < β := μ.staticThreshold_pos.trans hgt
  rw [hlaw] at hrest
  have hY := markY_sq_from_contact μ hβ hx hQ hrest.1 hrest.2.1
  have hZ := markZ_div_markY (x := x) hβ hQ
  have hZlt : markZ x Q/markY β Q < β := by
    rw [hZ]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hx.2 hβ
  obtain ⟨hfrac, hedge, hedgepos⟩ := markK_edge_from_contact μ hβ hx hQ hrest.2.2.1
  have hTAP := variationalValue_TAP μ hβ hx hQ hlaw hrest.1 hrest.2.1
  exact ⟨x, hx, Q, hQ, hlaw, hY, hZ, hZlt, hfrac, hedge, hedgepos, hTAP⟩

end

end SlowEquilibration.TwoAtomStationarity
