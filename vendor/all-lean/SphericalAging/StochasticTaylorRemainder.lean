module

public import SphericalAging.StochasticDifferenceQuotient
public import SphericalAging.LinearResolvent

public section

/-! Actual nonlinear coefficient Taylor errors in the full predictable
L² space. The estimate follows from the proved Fréchet Taylor bound and
an actual fourth-moment bound on the nonlinear path increment. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace SphericalAging.StochasticTaylorRemainder
open HardSphereDynamics LocalSDE VariationalCoefficients SecantCoefficient PredictableLinearCoefficient
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def remainder {X : ℝ≥0 → Ω → State N} (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g)
    (T : ℝ≥0) (U V : PredictableStateL2 N F P) : PredictableProcessL2 F P :=
  predictableCoefficient hL V T-predictableCoefficient hL U T-
    apply (derivativeRow X hXa hXc hg hL T) (V-U)

 theorem scalar_norm_sq (R : PredictableProcessL2 F P) :
    ‖R‖^2 = ∫ q,‖(R : TimeProcessL2 P) q‖^2 ∂nonnegativeLebesgueMeasure.prod P := by
  change ‖(R : TimeProcessL2 P)‖^2 = _
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  congr 1
  funext q
  exact real_inner_self_eq_norm_sq _

 theorem remainder_coeFn {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    {K : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g) :
    (remainder hXa hXc hg hL T U V : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1 ∈ Ioc 0 T then g (Y q.1 q.2)-g (X q.1 q.2)-
        fderiv ℝ g (X q.1 q.2) (Y q.1 q.2-X q.1 q.2) else 0) := by
  filter_upwards [Lp.coeFn_sub
      ((predictableCoefficient hL V T-predictableCoefficient hL U T : PredictableProcessL2 F P) : TimeProcessL2 P)
      (apply (derivativeRow X hXa hXc hg hL T) (V-U)),
    Lp.coeFn_sub (predictableCoefficient hL V T : TimeProcessL2 P) (predictableCoefficient hL U T),
    apply_coeFn (derivativeRow X hXa hXc hg hL T) (V-U),
    Lp.coeFn_sub (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) U,
    predictableCoefficient_coeFn hL V T,predictableCoefficient_coeFn hL U T,hXeq,hYeq]
      with q hsub hsub' ha hd hv hu hx hy
  simp only [Submodule.coe_sub] at hsub hsub' ha hd ⊢
  change (((predictableCoefficient hL V T : TimeProcessL2 P)-(predictableCoefficient hL U T : TimeProcessL2 P))-
    (apply (derivativeRow X hXa hXc hg hL T) (V-U) : TimeProcessL2 P)) q = _
  rw [hsub,Pi.sub_apply,hsub',Pi.sub_apply,ha,hd,Pi.sub_apply,hv,hu]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · have hx' : X q.1 q.2 = (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [indicator_of_mem (show q ∈ Ioc 0 T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hx
    have hy' : Y q.1 q.2 = (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [indicator_of_mem (show q ∈ Ioc 0 T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hy
    simp only [derivativeRow,ht,ite_true,← hx',← hy']
  · simp only [derivativeRow,ht,ite_false,zero_apply,sub_self]

 theorem norm_remainder_sq_le {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    {K L : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g)
    (hder : LipschitzWith L (fderiv ℝ g))
    (hfour : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P)) :
    ‖remainder hXa hXc hg hL T U V‖^2 ≤ (L : ℝ)^2 *
      ∫ q, ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
        (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P := by
  rw [scalar_norm_sq,← integral_const_mul]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun q => sq_nonneg _))
    (hfour.const_mul ((L : ℝ)^2))
  filter_upwards [remainder_coeFn hXa hXc hXeq hYeq hg hL] with q hq
  rw [hq]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [ht,ite_true,indicator_of_mem (show q ∈ Ioc 0 T ×ˢ (univ : Set Ω)
      from ⟨ht,mem_univ _⟩)]
    have h := taylor_remainder_bound hg hder (X q.1 q.2) (Y q.1 q.2)
    have hs := mul_self_le_mul_self (norm_nonneg _) h
    convert hs using 1 <;> ring
  · simp [ht]

 theorem norm_remainder_le {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    {K L : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g)
    (hder : LipschitzWith L (fderiv ℝ g))
    (hfour : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P))
    (C : ℝ) (hC : 0 ≤ C) (v : State N)
    (hbound : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤ C*‖v‖^4) :
    ‖remainder hXa hXc hg hL T U V‖ ≤ (L : ℝ)*Real.sqrt C*‖v‖^2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (L : ℝ)^2 * (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
        (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) :=
      norm_remainder_sq_le hXa hXc hXeq hYeq hg hL hder hfour
    _ ≤ (L : ℝ)^2*(C*‖v‖^4) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hC];ring
end SphericalAging.StochasticTaylorRemainder
