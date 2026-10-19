module

public import SphericalAging.LocalSDE
public import Mathlib.Analysis.SpecialFunctions.Exp

public section

/-! The bounded invertible exponential multiplier on the actual closed
predictable product L² space. It supplies a complete Banach space for Picard
on every finite horizon without changing the driving filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.WeightedPredictable
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] abbrev PredictableL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) :=
  lpMeas E ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P)

theorem time_stronglyMeasurable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    StronglyMeasurable[F.predictable] (fun q : ℝ≥0 × Ω => q.1) := by
  apply Measurable.stronglyMeasurable
  apply measurable_of_Ioi
  intro t
  convert (measurableSet_predictable_Ioi_prod (𝓕 := F) (i := t)
    (show MeasurableSet[F t] (univ : Set Ω) from MeasurableSet.univ)) using 1
  ext q
  simp

@[expose] def weight (α : ℝ) (T t : ℝ≥0) : ℝ := Real.exp (-α * (min t T : ℝ≥0))

theorem weight_pos (α : ℝ) (T t : ℝ≥0) : 0 < weight α T t := Real.exp_pos _

theorem weight_continuous (α : ℝ) (T : ℝ≥0) : Continuous (weight α T) := by
  unfold weight
  fun_prop

theorem weight_stronglyMeasurable (α : ℝ) (T : ℝ≥0) :
    StronglyMeasurable[F.predictable] (fun q : ℝ≥0 × Ω => weight α T q.1) :=
  (weight_continuous α T).comp_stronglyMeasurable (time_stronglyMeasurable F)

theorem weight_le (α : ℝ) (T t : ℝ≥0) : weight α T t ≤ Real.exp (|α| * T) := by
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right (neg_le_abs α) (min t T).coe_nonneg).trans
    (mul_le_mul_of_nonneg_left (show (min t T : ℝ≥0) ≤ T from min_le_right _ _) (abs_nonneg _))

theorem weight_mul_inverse (α : ℝ) (T t : ℝ≥0) : weight α T t * weight (-α) T t = 1 := by
  rw [weight, weight, ← Real.exp_add]
  have heq : -α * (min t T : ℝ≥0) + - -α * (min t T : ℝ≥0) = 0 := by ring
  rw [heq, Real.exp_zero]

theorem weighted_memLp (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    MemLp (fun q => weight α T q.1 • (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  apply (Lp.memLp (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P))).of_le_mul (c := Real.exp (|α| * T))
    (((weight_stronglyMeasurable (F := F) α T).aestronglyMeasurable.smul
      (lpMeas.aestronglyMeasurable U)).mono (predictable_le_prod F))
  exact .of_forall (fun q => by
    change ‖weight α T q.1 • (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖ ≤
      Real.exp (|α| * T) * ‖(U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖
    rw [norm_smul, Real.norm_of_nonneg (weight_pos α T q.1).le]
    exact mul_le_mul_of_nonneg_right (weight_le α T q.1) (norm_nonneg _))

@[expose] def multiply (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) : PredictableL2 E F P :=
  ⟨(weighted_memLp α T U).toLp _,
    ((weight_stronglyMeasurable (F := F) α T).aestronglyMeasurable.smul
      (lpMeas.aestronglyMeasurable U)).congr (weighted_memLp α T U).coeFn_toLp.symm⟩

theorem multiply_coeFn (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    (multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => weight α T q.1 • (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q) :=
  (weighted_memLp α T U).coeFn_toLp

theorem norm_multiply_le (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    ‖multiply α T U‖ ≤ Real.exp (|α| * T) * ‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_coeFn α T U] with q hq
  change ‖(multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖ ≤
    Real.exp (|α| * T) * ‖(U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖
  rw [hq, norm_smul, Real.norm_of_nonneg (weight_pos α T q.1).le]
  exact mul_le_mul_of_nonneg_right (weight_le α T q.1) (norm_nonneg _)

theorem multiply_add (α : ℝ) (T : ℝ≥0) (U V : PredictableL2 E F P) :
    multiply α T (U + V) = multiply α T U + multiply α T V := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (U+V), multiply_coeFn α T U, multiply_coeFn α T V,
    Lp.coeFn_add (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) V,
    Lp.coeFn_add (multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) (multiply α T V)]
    with q hsum hU hV hUV hmul
  simpa only [Submodule.coe_add, Pi.add_apply, hsum, hU, hV, hUV, smul_add] using hmul.symm

theorem multiply_sub (α : ℝ) (T : ℝ≥0) (U V : PredictableL2 E F P) :
    multiply α T (U - V) = multiply α T U - multiply α T V := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (U-V), multiply_coeFn α T U, multiply_coeFn α T V,
    Lp.coeFn_sub (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) V,
    Lp.coeFn_sub (multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) (multiply α T V)]
    with q hsum hU hV hUV hmul
  simpa only [Submodule.coe_sub, Pi.sub_apply, hsum, hU, hV, hUV, smul_sub] using hmul.symm

theorem multiply_zero (α : ℝ) (T : ℝ≥0) : multiply (E := E) (F := F) (P := P) α T 0 = 0 := by
  have h := multiply_sub (E := E) (F := F) (P := P) α T 0 0
  simpa only [sub_self] using h

theorem multiply_smul (α : ℝ) (T : ℝ≥0) (c : ℝ) (U : PredictableL2 E F P) :
    multiply α T (c • U) = c • multiply α T U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (c • U), multiply_coeFn α T U,
    Lp.coeFn_smul c (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)),
    Lp.coeFn_smul c (multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P))]
    with q hsum hU hc hmul
  simpa only [Submodule.coe_smul, Pi.smul_apply, hsum, hU, hc, smul_smul,
    mul_comm (weight α T q.1) c] using hmul.symm

theorem multiply_sum {ι : Type*} (α : ℝ) (T : ℝ≥0) (s : Finset ι)
    (U : ι → PredictableL2 E F P) : multiply α T (∑ i ∈ s, U i) = ∑ i ∈ s, multiply α T (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multiply_zero]
  | @insert i s hi ih => simp [hi, multiply_add, ih]

section StateCoefficients
open HardSphereDynamics PredictableItoTime
variable {N : ℕ} [IsProbabilityMeasure P]

theorem multiply_scalarToState (α : ℝ) (T : ℝ≥0) (i : Fin N)
    (U : PredictableProcessL2 F P) :
    multiply α T (scalarToStatePredictable i U) = scalarToStatePredictable i (multiply α T U) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (scalarToStatePredictable i U), multiply_coeFn α T U,
    LocalSDE.scalarToStatePredictable_coeFn i U,
    LocalSDE.scalarToStatePredictable_coeFn i (multiply α T U)] with q hweight hU hspan hspanW
  simp only [hweight, hU, hspan, hspanW, smul_eq_mul, smul_smul]

theorem norm_weighted_coefficient_sub_le
    {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) (α : ℝ) (T : ℝ≥0)
    (U V : PredictableStateL2 N F P) :
    ‖multiply α T (predictableCoefficient hg U T - predictableCoefficient hg V T)‖ ≤
      (K : ℝ) * ‖multiply α T (U-V)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_coeFn α T (predictableCoefficient hg U T - predictableCoefficient hg V T),
    multiply_coeFn α T (U-V), predictableCoefficient_coeFn hg U T, predictableCoefficient_coeFn hg V T,
    Lp.coeFn_sub (predictableCoefficient hg U T : TimeProcessL2 P) (predictableCoefficient hg V T),
    Lp.coeFn_sub (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) V]
    with q hweighted hstate hU hV hcoeffsub hstatesub
  change ‖(multiply α T (predictableCoefficient hg U T - predictableCoefficient hg V T) :
      TimeProcessL2 P) q‖ ≤ (K : ℝ) *
    ‖(multiply α T (U-V) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖
  rw [hweighted, hstate]
  simp only [Submodule.coe_sub, hcoeffsub, hstatesub, Pi.sub_apply, hU, hV]
  by_cases hqt : q.1 ∈ Ioc 0 T
  · simp only [hqt, ite_true, norm_smul, Real.norm_of_nonneg (weight_pos α T q.1).le]
    have hlip : ‖g ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q) -
        g ((V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q)‖ ≤
        (K : ℝ) * ‖(U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q -
          (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖ :=
      hg.norm_sub_le _ _
    nlinarith [mul_le_mul_of_nonneg_left hlip (weight_pos α T q.1).le]
  · simp only [hqt, ite_false, sub_self, smul_zero, norm_zero]
    exact mul_nonneg K.coe_nonneg (norm_nonneg _)
end StateCoefficients

theorem multiply_inverse (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    multiply α T (multiply (-α) T U) = U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (multiply (-α) T U), multiply_coeFn (-α) T U] with q hq hU
  simp only [hq, hU, smul_smul, weight_mul_inverse, one_smul]

theorem inverse_multiply (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    multiply (-α) T (multiply α T U) = U := by
  simpa only [neg_neg] using multiply_inverse (-α) T U

theorem multiply_injective (α : ℝ) (T : ℝ≥0) :
    Function.Injective (multiply (E := E) (F := F) (P := P) α T) := by
  intro U V h
  have hi := congrArg (multiply (-α) T) h
  simpa only [inverse_multiply] using hi

end SphericalAging.WeightedPredictable
