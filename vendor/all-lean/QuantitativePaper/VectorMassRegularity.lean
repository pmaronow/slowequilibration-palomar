module
public import QuantitativePaper.VectorRecursion
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

/-! The expectation branch of the actual vector Cole--Hopf transform is the
analytic removable value of its log-Laplace quotient. This gives genuine mass
regularity through zero without assuming normalized-CGF convexity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem vectorStep_integrableExpSet {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) :
    integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)=univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro m
  exact integrable_exp_vectorStep f K hf v m x

theorem vectorColeHopfStep_eq_dslope_cgf {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) :
    (fun m => vectorColeHopfStep v m f x)=
      dslope (cgf (fun z => f (fieldShift v x z)) (fieldGaussian n)) 0 := by
  funext m
  by_cases hm : m=0
  · subst m
    have hmem : (0 : ℝ)∈interior
        (integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
      rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
      trivial
    simp [vectorColeHopfStep,deriv_cgf_zero hmem]
  · rw [dslope_of_ne _ hm]
    simp [slope,vsub_eq_sub,cgf,mgf,vectorColeHopfStep,vectorStepPartition,hm,div_eq_mul_inv,mul_comm]

theorem analyticAt_vectorColeHopfStep_mass {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) (m : ℝ) :
    AnalyticAt ℝ (fun a => vectorColeHopfStep v a f x) m := by
  have hmem (a : ℝ) : a∈interior
      (integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
    rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
    trivial
  by_cases hm : m=0
  · subst m
    rw [vectorColeHopfStep_eq_dslope_cgf f K hf v x]
    obtain ⟨p,hp⟩ := analyticAt_cgf (hmem 0)
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · apply ((analyticAt_cgf (hmem m)).div analyticAt_id hm).congr
    filter_upwards [eventually_ne_nhds hm] with a ha
    simp [vectorColeHopfStep,vectorStepPartition,ha,cgf,mgf,div_eq_mul_inv,mul_comm]

theorem differentiable_vectorColeHopfStep_mass {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) :
    Differentiable ℝ (fun m => vectorColeHopfStep v m f x) :=
  fun m => (analyticAt_vectorColeHopfStep_mass f K hf v x m).differentiableAt

theorem hasDerivAt_vectorColeHopfStep_mass_zero {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) :
    HasDerivAt (fun m => vectorColeHopfStep v m f x)
      ((∫z,(f (fieldShift v x z)-vectorColeHopfStep v 0 f x)^2 ∂fieldGaussian n)/2) 0 := by
  have hmem : (0 : ℝ)∈interior
      (integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
    rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
    trivial
  have H := (analyticAt_cgf hmem).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.deriv
  have Hd : deriv (dslope (cgf (fun z => f (fieldShift v x z)) (fieldGaussian n)) 0) 0=
      iteratedDeriv 2 (cgf (fun z => f (fieldShift v x z)) (fieldGaussian n)) 0/2 := by
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using! H
  apply (analyticAt_vectorColeHopfStep_mass f K hf v x 0).differentiableAt.hasDerivAt.congr_deriv
  rw [vectorColeHopfStep_eq_dslope_cgf f K hf v x,Hd,iteratedDeriv_two_cgf_eq_integral hmem]
  simp [deriv_cgf_zero hmem,vectorColeHopfStep]

end QuantitativePaper
