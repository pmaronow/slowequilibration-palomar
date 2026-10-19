-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinKernels
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Exact composition of ordinary Gibbs preparations on the actual spin
space. Normalizing the base field first and then the perturbation gives
exactly the Gibbs law of their sum. No pressure or overlap theorem is a
hypothesis, and the base reference measure may be singular. -/

namespace SlowEquilibration.SphericalParisiGibbsTilt
noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [MeasurableSpace V]

def scalarPartition (ν : Measure V) (f : V → ℝ) : ℝ := ∫ z,Real.exp (f z) ∂ν

def scalarGibbs (ν : Measure V) (f : V → ℝ) : Measure V :=
  ν.withDensity (fun z => ENNReal.ofReal (Real.exp (f z)/scalarPartition ν f))

theorem scalar_exp_integrable (ν : Measure V) [IsFiniteMeasure ν]
    (f : V → ℝ) (hf : Measurable f) {B : ℝ} (hb : ∀ᵐ z ∂ν,|f z| ≤ B) :
    Integrable (fun z => Real.exp (f z)) ν := by
  apply Integrable.of_bound hf.exp.aestronglyMeasurable (Real.exp B)
  exact hb.mono fun z hz => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hz)

theorem scalarPartition_pos (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (f : V → ℝ) (hf : Measurable f) {B : ℝ} (hb : ∀ᵐ z ∂ν,|f z| ≤ B) :
    0 < scalarPartition ν f := integral_exp_pos (scalar_exp_integrable ν f hf hb)

/-- Actual normalized positive Gibbs density is a probability law. -/
theorem scalarGibbs_probability (ν : Measure V) [IsProbabilityMeasure ν]
    (f : V → ℝ) (hf : Measurable f) {B : ℝ} (hb : ∀ᵐ z ∂ν,|f z| ≤ B) :
    IsProbabilityMeasure (scalarGibbs ν f) := by
  have hp := scalarPartition_pos ν f hf hb
  have hi := (scalar_exp_integrable ν f hf hb).div_const (scalarPartition ν f)
  constructor
  rw [scalarGibbs,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun z =>
      (div_pos (Real.exp_pos _) hp).le),integral_div]
  change ENNReal.ofReal (scalarPartition ν f/scalarPartition ν f)=1
  rw [div_self hp.ne',ENNReal.ofReal_one]

theorem scalarGibbs_absolutelyContinuous (ν : Measure V) (f : V → ℝ) :
    scalarGibbs ν f ≪ ν := withDensity_absolutelyContinuous _ _

/-- Exact normalized integral after the first actual Gibbs tilt. -/
theorem scalarPartition_after_tilt (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (f g : V → ℝ) (hf : Measurable f) {B : ℝ} (hb : ∀ᵐ z ∂ν,|f z| ≤ B) :
    scalarPartition (scalarGibbs ν f) g=scalarPartition ν (fun z => f z+g z)/scalarPartition ν f := by
  have hp := scalarPartition_pos ν f hf hb
  unfold scalarPartition scalarGibbs
  rw [integral_withDensity_eq_integral_toReal_smul
    ((hf.exp.div_const _).ennreal_ofReal) (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_pos (Real.exp_pos _) hp).le,smul_eq_mul]
  have he : (fun z => Real.exp (f z)/(∫ y,Real.exp (f y) ∂ν)*Real.exp (g z))=
      fun z => Real.exp (f z+g z)/(∫ y,Real.exp (f y) ∂ν) := by
    funext z
    rw [Real.exp_add]
    ring
  change (∫ z,Real.exp (f z)/(∫ y,Real.exp (f y) ∂ν)*Real.exp (g z) ∂ν)=_
  rw [he,integral_div]

/-- Literal equality of genuine Gibbs probability measures under two
successive bounded measurable tilts. -/
theorem actual_sequential_scalar_gibbs (ν : Measure V) [IsProbabilityMeasure ν]
    (f g : V → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hb : ∀ᵐ z ∂ν,|f z| ≤ B) (hc : ∀ᵐ z ∂ν,|g z| ≤ C) :
    scalarGibbs (scalarGibbs ν f) g=scalarGibbs ν (fun z => f z+g z) := by
  have hp := scalarPartition_pos ν f hf hb
  have hfg : ∀ᵐ z ∂ν,|f z+g z| ≤ B+C := hb.and hc |>.mono
    (fun z hz => (abs_add_le _ _).trans (add_le_add hz.1 hz.2))
  have hpfg := scalarPartition_pos ν (fun z => f z+g z) (hf.add hg) hfg
  have hz := scalarPartition_after_tilt ν f g hf hb
  unfold scalarGibbs at *
  rw [← withDensity_mul ν ((hf.exp.div_const _).ennreal_ofReal)
    ((hg.exp.div_const _).ennreal_ofReal)]
  apply withDensity_congr_ae
  exact .of_forall fun z => by
    rw [Pi.mul_apply,← ENNReal.ofReal_mul (div_pos (Real.exp_pos _) hp).le,hz]
    change ENNReal.ofReal (Real.exp (f z)/scalarPartition ν f*
      (Real.exp (g z)/(scalarPartition ν (fun z => f z+g z)/scalarPartition ν f)))=
      ENNReal.ofReal (Real.exp (f z+g z)/scalarPartition ν (fun z => f z+g z))
    rw [Real.exp_add]
    congr 1
    field_simp [hp.ne',hpfg.ne']

theorem actual_gaussian_gibbs_eq_scalar {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) :
    gibbsMeasure ν L w=scalarGibbs ν (fun z => L z w) := by
  unfold gibbsMeasure scalarGibbs scalarPartition GaussianSpinInterpolation.moment weight
  simp only [one_mul]

end
end SlowEquilibration.SphericalParisiGibbsTilt
