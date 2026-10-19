-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSOneStepMarks
public import SlowEquilibration.ThermalPhysicalZeroContact

@[expose] public section

/-!
# The source strict one-step certificate and its actual variational consequences

The certificate below is precisely the pointwise integral certificate in
manuscript Definition 5.9. In particular, neither minimality, a physical
pressure limit, a ground-state formula, nor multisamplability is supplied as
an assumption. Ordinary CS minimality and the strictly superstatic conclusion
of Lemma 5.10 follow from the proved support criterion.
-/

namespace SlowEquilibration.SphericalTAPCertificate

noncomputable section
open MeasureTheory Set Filter CrisantiSommers CSParisiMeasure TwoAtomStationarity
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The literal ordinary integral strict-one-step certificate of the source. -/
structure Certificate (μ : FiniteMixture) (β x Q : ℝ) : Prop where
  min_degree : 4 ≤ μ.minDegree
  beta_pos : 0 < β
  weight_range : x ∈ Ioo (0 : ℝ) 1
  overlap_range : Q ∈ Ioo (0 : ℝ) 1
  contact_value : CSStructure.potential μ β (twoAtom x Q) Q = 0
  contact_derivative : deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0
  positive_off_contact : ∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q →
    0 < CSStructure.potential μ β (twoAtom x Q) r
  contact_curvature : 0 < deriv (deriv (CSStructure.potential μ β (twoAtom x Q))) Q

variable {μ : FiniteMixture} {β x Q : ℝ}

/-- Every source certificate gives an actual globally minimal admissible
probability law. This is proved directly, rather than a certificate field. -/
theorem Certificate.isMinimizer (h : Certificate μ β x Q) :
    (twoAtomAdmissible ⟨h.weight_range.1.le, h.weight_range.2.le⟩
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩).IsMinimizer β μ.xi := by
  let ζ := twoAtomAdmissible ⟨h.weight_range.1.le, h.weight_range.2.le⟩
    ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  have hξcont : ContinuousOn μ.xi (Ico (0 : ℝ) 1) :=
    fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  apply (ζ.minimizer_iff_support_on_maximum β μ.xi hξcont).mpr
  refine ⟨0, ?_, ?_⟩
  · intro r hr
    change firstVariation β μ.xi (twoAtom x Q) r ≤ 0
    by_cases hr0 : r = 0
    · simp [hr0, firstVariation, μ.xi_zero]
    by_cases hrQ : r = Q
    · have hh := h.contact_value
      unfold CSStructure.potential at hh
      simpa only [hrQ] using (neg_eq_zero.mp hh).le
    have hpos := h.positive_off_contact r
      ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hr.2⟩ hrQ
    exact (neg_pos.mp hpos).le
  · change ∀ᵐ r ∂twoAtom x Q, firstVariation β μ.xi (twoAtom x Q) r = 0
    rw [twoAtom, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      simp [firstVariation, μ.xi_zero]
    · apply Measure.ae_smul_measure
      simp only [ae_dirac_eq]
      exact neg_eq_zero.mp h.contact_value

/-- The certificate's two-atom measure is the actual unique canonical CS
minimizer. No thermodynamic identification is needed for this conclusion. -/
theorem Certificate.canonical_law (h : Certificate μ β x Q) :
    (canonicalMinimizer μ β).law = twoAtom x Q := by
  have heq := eq_canonicalMinimizer_of_isMinimizer μ β
    (twoAtomAdmissible ⟨h.weight_range.1.le, h.weight_range.2.le⟩
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩) h.isMinimizer
  exact (congrArg Admissible.law heq).symm

private theorem twoAtom_ne_diracZero {a q : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) : twoAtom a q ≠ Measure.dirac (0 : ℝ) := by
  intro heq
  have hq0 : q ≠ 0 := hq.1.ne'
  have hm := congrArg (fun ν : Measure ℝ => ν {q}) heq
  have hh : 1 ≤ a := by
    simpa [twoAtom, Measure.add_apply, Measure.smul_apply, hq0, Ne.symm hq0] using hm
  exact not_le_of_gt ha.2 hh

/-- Manuscript Lemma 5.10: every source strict-one-step certificate lies
strictly above the actual static threshold, including its endpoint. -/
theorem Certificate.superstatic (h : Certificate μ β x Q) :
    Thresholds.staticThreshold μ.xi < β := by
  by_contra hnot
  have hle : β ≤ Thresholds.staticThreshold μ.xi := le_of_not_gt hnot
  have hzero := (canonicalMinimizer_law_eq_diracZero_iff μ h.beta_pos.le).mpr hle
  rw [h.canonical_law] at hzero
  exact twoAtom_ne_diracZero h.weight_range h.overlap_range hzero

/-- The source's first two stationarity equations are genuine consequences
of the pointwise certificate for the actual covariance and law. -/
theorem Certificate.contact_equations (h : Certificate μ β x Q) :
    β ^ 2 * μ.xi1 Q = Q / ((1-Q) * profileConstant x Q) ∧
    β ^ 2 * x ^ 2 * μ.xi Q =
      Real.log (profileConstant x Q / (1-Q)) - x * Q / profileConstant x Q := by
  have hh := TwoAtomStationarity.contact_equations μ β h.weight_range h.overlap_range
    h.contact_value h.contact_derivative
  constructor
  · simpa only [mul_comm] using hh.1
  · have hx : x ≠ 0 := h.weight_range.1.ne'
    have hs := (eq_div_iff (pow_ne_zero 2 hx)).mp hh.2
    nlinarith only [hs]

/-- Source Proposition 5.11(1), its ordinary variational pressure clause.
The physical limiting pressure remains a separate Parisi obligation. -/
theorem Certificate.variational_pressure (h : Certificate μ β x Q) :
    variationalValue μ β =
      (β ^ 2 * (μ.xi 1-(1-x)*μ.xi Q) +
        Real.log (profileConstant x Q/(1-Q))/x + Real.log (1-Q))/2 :=
  variationalValue_of_twoAtom μ β h.weight_range h.overlap_range h.canonical_law

/-- The exact scalar TAP identity follows from the certificate and the
actual existing canonical minimizer, without a ground-energy premise. -/
theorem Certificate.variational_TAP (h : Certificate μ β x Q) :
    variationalValue μ β = β * markE μ β x Q + Real.log (1-Q)/2 +
      β ^ 2 * residualAtOne μ Q / 2 :=
  variationalValue_TAP μ h.beta_pos h.weight_range h.overlap_range
    h.canonical_law h.contact_value h.contact_derivative

/-- The strict source Hessian edge margin is derived from contact curvature. -/
theorem Certificate.edge_margin (h : Certificate μ β x Q) :
    markB μ Q / (markY β Q) ^ 2 < 1 ∧
      markK μ β Q - 2 * Real.sqrt (markB μ Q) =
        (markY β Q - Real.sqrt (markB μ Q)) ^ 2 / markY β Q ∧
      0 < markK μ β Q - 2 * Real.sqrt (markB μ Q) :=
  markK_edge_from_contact μ h.beta_pos h.weight_range h.overlap_range h.contact_curvature

end
end SlowEquilibration.SphericalTAPCertificate
