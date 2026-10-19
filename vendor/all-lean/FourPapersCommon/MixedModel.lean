module
public import FourPapersCommon.Mixture
public import FRSB.OptimalDiffusion
public import Paper.ParisiSelectedMoment
public import Paper.ParisiCurvature
public import FRSB.ConstantMassParity

@[expose] public section

/-! Genuine mixed even-spin Parisi objects under the normalized variance clock.
The original overlap coordinate remains in the mixed functional correction.
The objects reuse the constructed arbitrary-measure PDE and Brownian state;
no minimizer, physical Parisi formula, or mixed-model identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 300000

abbrev ParisiMeasure := Paper.ParisiMeasure
abbrev Overlap := Paper.Overlap
abbrev BrownianSample := Paper.BrownianSample

def mixedMeasure (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) : ParisiMeasure :=
  μ.map ξ.unitClock

def mixedBeta (ξ : AdmissibleEvenMixture) : ℝ := Real.sqrt ξ.variance

theorem mixedBeta_pos (ξ : AdmissibleEvenMixture) : 0 < mixedBeta ξ :=
  Real.sqrt_pos.mpr ξ.variance_pos

theorem mixedBeta_ne_zero (ξ : AdmissibleEvenMixture) : mixedBeta ξ ≠ 0 :=
  (mixedBeta_pos ξ).ne'

@[simp] theorem mixedBeta_sq (ξ : AdmissibleEvenMixture) : mixedBeta ξ ^ 2=ξ.variance :=
  Real.sq_sqrt ξ.variance_pos.le

/-- Exact cumulative mass transport, including every atom. -/
theorem parisiCDF_mixedMeasure (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    Paper.parisiCDF (mixedMeasure ξ μ) (ξ.clock q)=Paper.parisiCDF μ q := by
  have hm : MeasurableSet {r : Overlap | (r:ℝ)≤ξ.clock q} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  unfold Paper.parisiCDF mixedMeasure
  rw [ProbabilityMeasure.map_apply' μ ξ.continuous_unitClock.measurable.aemeasurable hm]
  congr 1
  congr 1
  ext r
  change ξ.clock (r:ℝ)≤ξ.clock q ↔ (r:ℝ)≤q
  exact ξ.clock_strictMonoOn.le_iff_le r.property hq

def mixedPotential (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  Paper.parisiPotential (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock p.1,p.2)

def mixedGradient (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  Paper.parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock p.1,p.2)

def mixedHessian (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) (p : ℝ×ℝ) : ℝ :=
  Paper.parisiHessian (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock p.1,p.2)

def mixedSpatialJet (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (j : ℕ) (q x : ℝ) : ℝ :=
  FRSB.parisiSpatialJet (mixedBeta ξ) (mixedMeasure ξ μ) j (ξ.clock q) x

/-- The constructed pathwise diffusion at the genuine variance time. -/
def mixedState (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    (sample : BrownianSample) (q : ℝ) : ℝ :=
  Paper.selectedParisiStateReal (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) sample (ξ.clock q)

/-- Actual squared magnetization, evaluated along the actual mixed state. -/
def mixedGamma (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  ∫ sample,mixedGradient ξ μ (q,mixedState ξ h μ sample q)^2
    ∂Paper.canonicalBrownianMeasure

/-- Mixed-model correction in the original overlap coordinate. -/
def mixedFunctional (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure) : ℝ :=
  Real.log 2+mixedPotential ξ μ (0,h)-
    (1/2:ℝ)*∫q in (0:ℝ)..1,q*ξ.second q*Paper.parisiCDF μ q

def mixedPressure (ξ : AdmissibleEvenMixture) (h : ℝ) : ℝ :=
  sInf (Set.range (mixedFunctional ξ h))

def IsMixedMinimizer (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure) : Prop :=
  ∀ ν : ParisiMeasure,mixedFunctional ξ h μ ≤ mixedFunctional ξ h ν

/-- The manuscript's first variation, with lower integration limit zero. -/
def mixedFirstVariation (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) : ℝ :=
  (1/2:ℝ)*∫s in (0:ℝ)..q,ξ.second s*(mixedGamma ξ h μ s-s)

@[simp] theorem mixedPotential_terminal (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (x : ℝ) : mixedPotential ξ μ (1,x)=Real.log (Real.cosh x) := by
  simp only [mixedPotential,ξ.clock_one,Paper.parisiPotential_terminal]

@[simp] theorem mixedState_initial (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (sample : BrownianSample) : mixedState ξ h μ sample 0=h := by
  simp only [mixedState,ξ.clock_zero,Paper.selectedParisiState_initial]

@[simp] theorem mixedFirstVariation_zero (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) : mixedFirstVariation ξ h μ 0= 0 := by
  simp only [mixedFirstVariation,intervalIntegral.integral_same,mul_zero]

theorem mixedGamma_eq_selected (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) :
    mixedGamma ξ h μ q=Paper.selectedParisiSecondMoment (mixedBeta ξ) h
      (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ) (ξ.clock q) := rfl

theorem mixedGamma_nonneg (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) : 0 ≤ mixedGamma ξ h μ q :=
  integral_nonneg (fun _ =>sq_nonneg _)

theorem mixedGamma_le_one (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : ℝ) : mixedGamma ξ h μ q ≤ 1 :=
  Paper.selectedParisiSecondMoment_le_one (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock q)

theorem hasDerivAt_mixedPotential_spatial (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    HasDerivAt (fun y=>mixedPotential ξ μ (q,y)) (mixedGradient ξ μ (q,x)) x := by
  change HasDerivAt (fun y=>Paper.parisiPotential (mixedBeta ξ) (mixedMeasure ξ μ)
    (ξ.clock q,y)) (Paper.parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock q,x)) x
  exact Paper.hasDerivAt_parisiPotential_spatial_all (mixedBeta ξ) (mixedMeasure ξ μ)
    (ξ.clock q) x (ξ.clock_mem_unitInterval hq)

theorem hasDerivAt_mixedGradient_spatial (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (q x : ℝ) :
    HasDerivAt (fun y=>mixedGradient ξ μ (q,y)) (mixedHessian ξ μ (q,x)) x := by
  simpa only [mixedGradient,mixedHessian,Paper.parisiHessianBCF_apply] using
    Paper.hasDerivAt_parisiGradient_spatial (mixedBeta ξ) (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) (ξ.clock q) x

theorem norm_mixedGradient_le_one (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (p : ℝ×ℝ) : ‖mixedGradient ξ μ p‖ ≤ 1 := Paper.norm_parisiGradient_le_one (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock p.1,p.2)

theorem mixedHessian_add_gradient_sq_le_one (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (p : ℝ×ℝ) : mixedHessian ξ μ p+mixedGradient ξ μ p^2 ≤ 1 :=
  Paper.parisiHessian_add_gradient_sq_le_one (mixedBeta ξ) (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock p.1,p.2)

theorem mixedHessian_pos (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) : 0 < mixedHessian ξ μ (q,x) :=
  Paper.parisiHessian_pos (mixedBeta ξ) (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ)
    (ξ.clock q) x (ξ.clock_mem_unitInterval hq)

theorem mixedPotential_even (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    mixedPotential ξ μ (q,-x)=mixedPotential ξ μ (q,x) :=
  FRSB.parisiPotential_even (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock q) x
    (ξ.clock_mem_unitInterval hq)

theorem mixedGradient_at_zero (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : mixedGradient ξ μ (q,0)= 0 :=
  FRSB.parisiGradient_at_zero (mixedBeta ξ) (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ)
    (ξ.clock q) (ξ.clock_mem_unitInterval hq)

@[simp] theorem mixedGamma_zero (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) :
    mixedGamma ξ 0 μ 0= 0 := by
  simp only [mixedGamma,mixedState_initial,mixedGradient_at_zero ξ μ 0 (by norm_num),
    zero_pow (by norm_num : 2≠0),integral_zero]

theorem mixedPotential_continuous_strip (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) :
    Continuous (fun p : Overlap×ℝ=>mixedPotential ξ μ (p.1,p.2)) :=
  (Paper.continuous_parisiPotential _ _).comp
    ((continuous_subtype_val.comp (ξ.continuous_unitClock.comp continuous_fst)).prodMk continuous_snd)

theorem mixedGradient_continuous_strip (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure) :
    Continuous (fun p : Overlap×ℝ=>mixedGradient ξ μ (p.1,p.2)) :=
  (Paper.continuous_parisiGradient _ _).comp
    ((continuous_subtype_val.comp (ξ.continuous_unitClock.comp continuous_fst)).prodMk continuous_snd)

theorem continuousOn_mixedGamma (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) : ContinuousOn (mixedGamma ξ h μ) (Icc (0:ℝ) 1) := by
  exact (Paper.continuousOn_selectedParisiSecondMoment _ h (mixedBeta_ne_zero ξ) _).comp
    ξ.continuousOn_clock (fun _ hq=>ξ.clock_mem_unitInterval hq)

end FourPapersCommon
