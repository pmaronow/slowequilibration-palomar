module
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

/-! The removable singularity of the actual normalized logarithmic moment.
This file proves analyticity and its variance derivative at zero. It does not
assert the separate Gaussian convexity theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem analyticAt_dslope_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    AnalyticAt ℝ (dslope f 0) 0 := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

theorem deriv_dslope_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    deriv (dslope f 0) 0=iteratedDeriv 2 f 0/2 := by
  let g := dslope f 0
  have hg : AnalyticAt ℝ g 0 := analyticAt_dslope_zero hf
  have he : (fun x : ℝ => f x-f 0)=fun x => x*g x := by
    funext x
    simpa only [sub_zero,smul_eq_mul,g] using (sub_smul_dslope f 0 x).symm
  have hd : deriv f=ᶠ[𝓝 0] fun x => g x+x*deriv g x := by
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with x hfx hgx
    have hh := (hasDerivAt_id x).mul hgx.differentiableAt.hasDerivAt
    have hh' : HasDerivAt (fun y => f y-f 0) (g x+x*deriv g x) x := by
      rw [he]
      convert! hh using 1 <;> simp only [id_eq,Pi.mul_apply,one_mul]
    exact (hfx.differentiableAt.hasDerivAt.sub_const (f 0)).unique hh'
  have hh := hg.differentiableAt.hasDerivAt.add
    ((hasDerivAt_id (0 : ℝ)).mul hg.deriv.differentiableAt.hasDerivAt)
  have hh' : HasDerivAt (fun x => g x+x*deriv g x) (2*deriv g 0) 0 := by
    convert! hh using 1 <;> simp [id_eq,Pi.mul_apply,Pi.add_apply] <;> ring
  have hsecond : iteratedDeriv 2 f 0=2*deriv g 0 := by
    rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hd.deriv_eq,hh'.deriv]
  rw [hsecond]
  change deriv g 0=2*deriv g 0/2
  ring

def normalizedCGF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : ℝ → ℝ :=
  dslope (cgf X P) 0

theorem normalizedCGF_of_ne {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) {lam : ℝ} (hlam : lam≠0) :
    normalizedCGF P X lam=cgf X P lam/lam := by
  rw [normalizedCGF,dslope_of_ne _ hlam]
  simp only [slope,sub_zero,cgf_zero,smul_eq_mul,vsub_eq_sub]
  ring

theorem normalizedCGF_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ)
    (h0 : 0∈interior (integrableExpSet X P)) :
    normalizedCGF P X 0=∫ω,X ω ∂P := by
  rw [normalizedCGF,dslope_same,deriv_cgf_zero h0]
  simp

theorem analyticAt_normalizedCGF_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (h0 : 0∈interior (integrableExpSet X P)) :
    AnalyticAt ℝ (normalizedCGF P X) 0 := analyticAt_dslope_zero (analyticAt_cgf h0)

theorem hasDerivAt_normalizedCGF_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ)
    (h0 : 0∈interior (integrableExpSet X P)) (hX : MemLp X 2 P) :
    HasDerivAt (normalizedCGF P X) (variance X P/2) 0 := by
  have hsecond : iteratedDeriv 2 (cgf X P) 0=variance X P := by
    rw [iteratedDeriv_two_cgf h0,variance_eq_sub hX]
    simp [deriv_cgf_zero h0]
  have hd : deriv (normalizedCGF P X) 0=variance X P/2 := by
    rw [normalizedCGF,deriv_dslope_zero (analyticAt_cgf h0),hsecond]
  exact hd ▸ (analyticAt_normalizedCGF_zero P X h0).differentiableAt.hasDerivAt

end FourPapersCommon
