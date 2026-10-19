-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CrisantiSommers
public import SlowEquilibration.CSVariation
public import SlowEquilibration.NonconvexCertificate

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set

/-- The manuscript's admissible measures, with their ordinary probability law.
The cutoff is a witness of compact support below one, not a parameter of the value. -/
structure Admissible where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  cutoff_exists : ∃ q, HasCutoff law q

instance (ζ : Admissible) : IsProbabilityMeasure ζ.law := ζ.probability

noncomputable def Admissible.cutoff (ζ : Admissible) : ℝ :=
  Classical.choose ζ.cutoff_exists

theorem Admissible.hasCutoff (ζ : Admissible) : HasCutoff ζ.law ζ.cutoff :=
  Classical.choose_spec ζ.cutoff_exists

/-- The ordinary functional with its proved independence of support cutoff. -/
noncomputable def Admissible.value (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ) : ℝ :=
  functional β η ζ.law ζ.cutoff

theorem Admissible.value_eq (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ)
    {q : ℝ} (hq : HasCutoff ζ.law q) :
    ζ.value β η = functional β η ζ.law q :=
  functional_cutoff_independent ζ.law β η ζ.hasCutoff hq

/-- Global minimization is over all compact-supported probability measures
below one, exactly the manuscript's variational class. -/
def Admissible.IsMinimizer (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ) : Prop :=
  ∀ μ : Admissible, ζ.value β η ≤ μ.value β η

theorem Admissible.minimizer_of_support_on_maximum (ζ : Admissible)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1)) (m : ℝ)
    (hmax : ∀ s ∈ Ico (0:ℝ) 1, firstVariation β η ζ.law s ≤ m)
    (hsupport : ∀ᵐ s ∂ζ.law, firstVariation β η ζ.law s = m) :
    ζ.IsMinimizer β η := by
  intro μ
  exact functional_minimal_of_firstVariation_maximum β η μ.law ζ.law
    μ.hasCutoff ζ.hasCutoff hη m hmax hsupport

/-- The literal one-step probability law x δ₀+(1-x) δQ. -/
noncomputable def twoAtom (x Q : ℝ) : Measure ℝ :=
  ENNReal.ofReal x • Measure.dirac 0 + ENNReal.ofReal (1-x) • Measure.dirac Q

theorem twoAtom_probability {x Q : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    IsProbabilityMeasure (twoAtom x Q) := by
  constructor
  simp only [twoAtom, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add hx.1 (sub_nonneg.mpr hx.2)]
  norm_num

theorem twoAtom_hasCutoff {x Q : ℝ} (hQ : Q ∈ Ico (0:ℝ) 1) :
    HasCutoff (twoAtom x Q) Q := by
  refine ⟨hQ.1,hQ.2,?_⟩
  rw [twoAtom, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨le_refl 0,hQ.1⟩
  · apply Measure.ae_smul_measure
    simp only [ae_dirac_eq]
    exact ⟨hQ.1,le_refl Q⟩

theorem integral_twoAtom {x Q : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (f : ℝ → ℝ) :
    (∫ s, f s ∂twoAtom x Q) = x*f 0+(1-x)*f Q := by
  have h0 : Integrable f (ENNReal.ofReal x • Measure.dirac (0:ℝ)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hQ : Integrable f (ENNReal.ofReal (1-x) • Measure.dirac Q) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [twoAtom, integral_add_measure h0 hQ, integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal hx.1,ENNReal.toReal_ofReal (sub_nonneg.mpr hx.2)]

/-- The piecewise one-step hatted profile is derived from the actual law. -/
theorem xHat_twoAtom {x Q : ℝ} (hx : x ∈ Icc (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    xHat (twoAtom x Q) r =
      if r ≤ Q then (1-Q+x*Q)-x*r else 1-r := by
  unfold xHat
  rw [integral_twoAtom hx]
  simp only [max_eq_left hr]
  split_ifs with h
  · rw [max_eq_right h]
    ring
  · rw [max_eq_left (le_of_not_ge h)]
    ring

noncomputable def twoAtomAdmissible {x Q : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (hQ : Q ∈ Ico (0:ℝ) 1) : Admissible :=
  ⟨twoAtom x Q,twoAtom_probability hx,⟨Q,twoAtom_hasCutoff hQ⟩⟩

end SlowEquilibration.CrisantiSommers

namespace SlowEquilibration.NonconvexCertificate

open MeasureTheory Set CrisantiSommers

/-- The actual probability measure asserted in the manuscript's degree-4/12 example. -/
noncomputable def exampleLaw : Admissible :=
  twoAtomAdmissible ⟨x_pos.le,parameters_mem.1.2.le⟩ ⟨Q_pos.le,Q_lt_one⟩

theorem exampleLaw_xHat {r : ℝ} (hr : 0 ≤ r) :
    CrisantiSommers.xHat exampleLaw.law r = xHat r := by
  rw [show exampleLaw.law = twoAtom x Q from rfl,
    xHat_twoAtom ⟨x_pos.le,parameters_mem.1.2.le⟩ hr, ← profile_constant]
  rfl

theorem exampleLaw_firstVariation {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    firstVariation beta xi exampleLaw.law r = -V r := by
  unfold firstVariation V
  rw [beta_sq]
  have heq : (∫ u in (0:ℝ)..r, (r-u)/(CrisantiSommers.xHat exampleLaw.law u)^2) =
      ∫ u in (0:ℝ)..r, (r-u)/(xHat u)^2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hr.1] at hu
    dsimp only
    rw [exampleLaw_xHat hu.1]
  rw [heq]
  ring

/-- The nonconvex certificate proves global minimality of the literal
one-step law for the ordinary Crisanti--Sommers functional. -/
theorem exampleLaw_minimizer : exampleLaw.IsMinimizer beta xi := by
  apply Admissible.minimizer_of_support_on_maximum exampleLaw beta xi
    (show ContinuousOn xi (Ico 0 1) from
      (continuous_iff_continuousAt.mpr (fun r => (xi_hasDerivAt r).continuousAt)).continuousOn) 0
  · intro r hr
    rw [exampleLaw_firstVariation hr]
    by_cases h0 : r=0
    · simp [h0,V_at_zero]
    by_cases hQ : r=Q
    · simp [hQ,contact_value]
    have hpos := strict_one_step_certificate.2.2.1 r
      ⟨lt_of_le_of_ne hr.1 (Ne.symm h0),hr.2⟩ hQ
    linarith
  · change ∀ᵐ s ∂twoAtom x Q, firstVariation beta xi (twoAtom x Q) s=0
    rw [twoAtom,ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      rw [ae_dirac_eq]
      have h := exampleLaw_firstVariation (r:=0) (by norm_num)
      simpa [exampleLaw,twoAtomAdmissible,twoAtom,V_at_zero] using h
    · apply Measure.ae_smul_measure
      rw [ae_dirac_eq]
      have h := exampleLaw_firstVariation (r:=Q) ⟨Q_pos.le,Q_lt_one⟩
      simpa [exampleLaw,twoAtomAdmissible,twoAtom,contact_value] using h

end SlowEquilibration.NonconvexCertificate
