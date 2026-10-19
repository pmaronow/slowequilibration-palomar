module
public import Paper.ItoLeftSums
public import Paper.HJBVerification

@[expose] public section

/-! Genuine stochastic left-sum identities with deterministic time shifts and
an identified generator. These are analytic tools, not supplied stochastic
identities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal
namespace FRSB

 theorem ito_stochastic_leftSums_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (T : ℝ≥0) (source : ℝ → Ω → ℝ)
    (hgen : ∀ ω, ∀ s ∈ Icc (0 : ℝ) (T : ℝ), hjbGenerator X d β f s ω=source s ω) :
    TendstoInMeasure P (fun n => uniformAdaptedMartingaleLeftSumProcess J
      (fun s ω => itoSpaceDerivative f s (X s ω)) T (n+1) T) atTop
      (fun ω => f T (X T ω)-f 0 (X 0 ω)-∫s in (0 : ℝ)..(T : ℝ),source s ω) := by
  have hconv := ito_stochastic_leftSums_tendstoInMeasure hc f hf htdiff hslice hdt hdx hsecond T
  apply TendstoInMeasure.congr_right _ hconv
  exact .of_forall fun ω => by
    have hi := hjbGenerator_integral_eq hc f hdt hdx hsecond T ω
    have hg : (∫s in (0 : ℝ)..(T : ℝ),hjbGenerator X d β f s ω)=
        ∫s in (0 : ℝ)..(T : ℝ),source s ω :=
      intervalIntegral.integral_congr_Ioo_of_le T.coe_nonneg
        (fun s hs => hgen ω s ⟨hs.1.le,hs.2.le⟩)
    linarith

 def timeShiftTest (f : ℝ → ℝ → ℝ) (a : ℝ) (t x : ℝ) : ℝ := f (a+t) x

 theorem timeShiftTest_timeDerivative (f : ℝ → ℝ → ℝ) (a t x : ℝ)
    (ht : ∀ x, Differentiable ℝ (fun s => f s x)) :
    itoTimeDerivative (timeShiftTest f a) t x=itoTimeDerivative f (a+t) x := by
  have hh := ((ht x (a+t)).hasDerivAt).comp t ((hasDerivAt_id t).const_add a)
  simpa only [itoTimeDerivative,timeShiftTest,Function.comp_def,mul_one] using hh.deriv

 theorem timeShiftTest_spaceDerivative (f : ℝ → ℝ → ℝ) (a t x : ℝ) :
    itoSpaceDerivative (timeShiftTest f a) t x=itoSpaceDerivative f (a+t) x := rfl

 theorem timeShiftTest_spaceSecondDerivative (f : ℝ → ℝ → ℝ) (a t x : ℝ) :
    itoSpaceSecondDerivative (timeShiftTest f a) t x=itoSpaceSecondDerivative f (a+t) x := rfl

 theorem timeShiftTest_regular (f : ℝ → ℝ → ℝ) (a : ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => timeShiftTest f a p.1 p.2) ∧
      (∀ x, Differentiable ℝ (fun s => timeShiftTest f a s x)) ∧
      (∀ s, ContDiff ℝ 2 (timeShiftTest f a s)) ∧
      Continuous (fun p : ℝ × ℝ => itoTimeDerivative (timeShiftTest f a) p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (timeShiftTest f a) p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (timeShiftTest f a) p.1 p.2) := by
  have hm : Continuous (fun p : ℝ × ℝ => (a+p.1,p.2)) := by fun_prop
  refine ⟨hf.comp hm,?_,fun t => hslice _,?_,hdx.comp hm,hsecond.comp hm⟩
  · intro x t
    exact (((htdiff x (a+t)).hasDerivAt).comp t ((hasDerivAt_id t).const_add a)).differentiableAt
  · simp_rw [timeShiftTest_timeDerivative f a _ _ htdiff]
    exact hdt.comp hm

end FRSB
