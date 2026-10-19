module

public import SphericalAging.SecantCoefficient

public section

/-! Actual predictable secant Jacobian coefficient rows along two nonlinear
SDE states, and the exact coefficient difference-quotient identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecantPredictable
open HardSphereDynamics LocalSDE VariationalCoefficients SecantCoefficient PredictableLinearCoefficient
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem row_timeCut_predictable (H : ℝ≥0 → Ω → (State N →L[ℝ] ℝ))
    (hHa : StronglyAdapted F H) (hHc : ∀ᵐ omega ∂P, Continuous (fun t => H t omega))
    (T : ℝ≥0) : AEStronglyMeasurable[F.predictable]
      (fun q : ℝ≥0 × Ω => if q.1 ∈ Ioc 0 T then H q.1 q.2 else 0)
      (nonnegativeLebesgueMeasure.prod P) := by
  classical
  have hi (i : Fin N) := FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
    (fun t omega => H t omega (basisVector i))
    (fun t => (ContinuousLinearMap.apply ℝ ℝ (basisVector i)).continuous.comp_stronglyMeasurable (hHa t))
    (hHc.mono (fun omega homega => (ContinuousLinearMap.apply ℝ ℝ (basisVector i)).continuous.comp homega)) T
  have hsum : AEStronglyMeasurable[F.predictable]
      (fun q : ℝ≥0 × Ω => ∑ i : Fin N, FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => H t omega (basisVector i)) T q • coordinate i)
      (nonnegativeLebesgueMeasure.prod P) :=
    by
      suffices hs : ∀ s : Finset (Fin N), AEStronglyMeasurable[F.predictable]
          (fun q : ℝ≥0 × Ω => ∑ i ∈ s, FourPapersCommon.continuousAdaptedTimeCut
            (fun t omega => H t omega (basisVector i)) T q • coordinate i)
          (nonnegativeLebesgueMeasure.prod P) from hs Finset.univ
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (aestronglyMeasurable_const (m := F.predictable)
          (μ := nonnegativeLebesgueMeasure.prod P) (b := (0 : State N →L[ℝ] ℝ)))
      | @insert i s his ih =>
        simpa only [Finset.sum_insert his] using
          continuous_add.comp_aestronglyMeasurable (((hi i).smul_const (coordinate i)).prodMk ih)
  apply hsum.congr
  apply Filter.Eventually.of_forall
  intro q
  apply ContinuousLinearMap.ext
  intro v
  by_cases ht : q.1 ∈ Ioc 0 T
  · simp only [ht,ite_true,sum_apply,smul_apply,
      coordinate_apply,smul_eq_mul,FourPapersCommon.continuousAdaptedTimeCut]
    have hh := congrArg (fun z : State N => H q.1 q.2 z) (state_sum_basis v)
    simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using hh
  · simp [ht,FourPapersCommon.continuousAdaptedTimeCut]


@[expose] def secantCoefficient (X Y : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g) (T : ℝ≥0) :
    Coefficient (N := N) (F := F) (P := P) K where
  value q := if q.1 ∈ Ioc 0 T then secantRow g (X q.1 q.2) (Y q.1 q.2) else 0
  measurable := row_timeCut_predictable _
    (fun t => (secantRow_continuous hg hL).comp_stronglyMeasurable ((hXa t).prodMk (hYa t)))
    (by
      filter_upwards [hXc,hYc] with omega hx hy
      exact (secantRow_continuous hg hL).comp (hx.prodMk hy)) T
  bound := .of_forall (fun q => by
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [ht,ite_true]
      exact secantRow_bound hL _ _
    · simp only [ht,ite_false,norm_zero]
      exact K.coe_nonneg)

/-- The genuine averaged Jacobian applied to an actual state difference
quotient is exactly the corresponding nonlinear coefficient quotient. -/
theorem secant_apply_difference {X Y : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
    {T : ℝ≥0} {U V : PredictableStateL2 N F P}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    {K : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g) (c : ℝ) :
    apply (secantCoefficient X Y hXa hYa hXc hYc hg hL T) (c • (V-U)) =
      c • (predictableCoefficient hL V T-predictableCoefficient hL U T) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [apply_coeFn (secantCoefficient X Y hXa hYa hXc hYc hg hL T) (c • (V-U)),
    Lp.coeFn_smul c ((V-U : PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)),
    Lp.coeFn_sub (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) U,
    Lp.coeFn_smul c ((predictableCoefficient hL V T-predictableCoefficient hL U T : PredictableProcessL2 F P) :
      Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)),
    Lp.coeFn_sub (predictableCoefficient hL V T : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P))
      (predictableCoefficient hL U T),predictableCoefficient_coeFn hL V T,
    predictableCoefficient_coeFn hL U T,hXeq,hYeq] with q ha hsm hs hsr hr hV hU hx hy
  change (apply (secantCoefficient X Y hXa hYa hXc hYc hg hL T) (c • (V-U)) :
      Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)) q =
    (c • ((predictableCoefficient hL V T-predictableCoefficient hL U T : PredictableProcessL2 F P) :
      Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P))) q
  simp only [Submodule.coe_smul,Submodule.coe_sub] at ha hsm hs hsr hr ⊢
  rw [ha,hsm,Pi.smul_apply,hs,Pi.sub_apply,hsr,Pi.smul_apply,hr,Pi.sub_apply,hV,hU]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · have hx' : X q.1 q.2 = (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hx
    have hy' : Y q.1 q.2 = (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hy
    simp only [secantCoefficient,ht,ite_true,map_smul,← hx',← hy',secantRow_increment hg]
  · simp only [secantCoefficient,ht,ite_false,zero_apply,sub_self,smul_zero]

end SphericalAging.SecantPredictable
