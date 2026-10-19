module

public import SphericalAging.WeightedPredictable

public section

/-! Actual random predictable bounded linear coefficient operators on the
closed predictable L² state space. These operators will be instantiated by
the true derivatives of the cutoff Hamiltonian drift and noise. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.PredictableLinearCoefficient
open HardSphereDynamics WeightedPredictable
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {K : ℝ≥0}

structure Coefficient (K : ℝ≥0) where
  value : ℝ≥0 × Ω → (State N →L[ℝ] ℝ)
  measurable : AEStronglyMeasurable[F.predictable] value (nonnegativeLebesgueMeasure.prod P)
  bound : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, ‖value q‖ ≤ K

theorem evaluation_measurable {K : ℝ≥0} (a : Coefficient (N := N) (F := F) (P := P) K)
    (U : PredictableStateL2 N F P) : AEStronglyMeasurable[F.predictable]
      (fun q => a.value q ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q))
      (nonnegativeLebesgueMeasure.prod P) :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (a.measurable.prodMk (lpMeas.aestronglyMeasurable U))

theorem evaluation_memLp {K : ℝ≥0} (a : Coefficient (N := N) (F := F) (P := P) K)
    (U : PredictableStateL2 N F P) : MemLp
      (fun q => a.value q ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q))
      2 (nonnegativeLebesgueMeasure.prod P) := by
  apply (Lp.memLp (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).of_le_mul
    ((evaluation_measurable a U).mono (predictable_le_prod F)) (c := (K : ℝ))
  filter_upwards [a.bound] with q hq
  exact (a.value q).le_of_opNorm_le hq _

@[expose] def apply (a : Coefficient (N := N) (F := F) (P := P) K)
    (U : PredictableStateL2 N F P) : PredictableProcessL2 F P :=
  ⟨(evaluation_memLp a U).toLp _,
    (evaluation_measurable a U).congr (evaluation_memLp a U).coeFn_toLp.symm⟩

theorem apply_coeFn (a : Coefficient (N := N) (F := F) (P := P) K)
    (U : PredictableStateL2 N F P) :
    (apply a U : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => a.value q ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q) :=
  (evaluation_memLp a U).coeFn_toLp

theorem apply_add (a : Coefficient (N := N) (F := F) (P := P) K)
    (U V : PredictableStateL2 N F P) : apply a (U+V) = apply a U + apply a V := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [apply_coeFn a (U+V),apply_coeFn a U,apply_coeFn a V,
    Lp.coeFn_add (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) V,
    Lp.coeFn_add (apply a U : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)) (apply a V)]
    with q hu hv hw hsum happ
  simpa only [Submodule.coe_add,hu,hv,hw,hsum,Pi.add_apply,map_add] using happ.symm

theorem apply_sub (a : Coefficient (N := N) (F := F) (P := P) K)
    (U V : PredictableStateL2 N F P) : apply a (U-V) = apply a U - apply a V := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [apply_coeFn a (U-V),apply_coeFn a U,apply_coeFn a V,
    Lp.coeFn_sub (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) V,
    Lp.coeFn_sub (apply a U : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)) (apply a V)]
    with q hu hv hw hsum happ
  simpa only [Submodule.coe_sub,hu,hv,hw,hsum,Pi.sub_apply,map_sub] using happ.symm

theorem apply_zero (a : Coefficient (N := N) (F := F) (P := P) K) : apply a 0 = 0 := by
  have h := apply_sub a 0 0
  simpa only [sub_self] using h

theorem apply_smul (a : Coefficient (N := N) (F := F) (P := P) K)
    (c : ℝ) (U : PredictableStateL2 N F P) : apply a (c • U) = c • apply a U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [apply_coeFn a (c • U),apply_coeFn a U,
    Lp.coeFn_smul c (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)),
    Lp.coeFn_smul c (apply a U : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P))]
    with q hu hv hsum happ
  simpa only [Submodule.coe_smul,hu,hv,hsum,Pi.smul_apply,map_smul] using happ.symm

theorem norm_apply_le (a : Coefficient (N := N) (F := F) (P := P) K)
    (U : PredictableStateL2 N F P) : ‖apply a U‖ ≤ (K : ℝ) * ‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [apply_coeFn a U,a.bound] with q hq hb
  change ‖(apply a U : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)) q‖ ≤
    (K : ℝ) * ‖(U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖
  rw [hq]
  exact (a.value q).le_of_opNorm_le hb _

theorem multiply_apply (a : Coefficient (N := N) (F := F) (P := P) K)
    (α : ℝ) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    multiply α T (apply a U) = apply a (multiply α T U) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [multiply_coeFn α T (apply a U),apply_coeFn a (multiply α T U),
    multiply_coeFn α T U,apply_coeFn a U] with q hu hv hm ha
  simp only [hu,hv,hm,ha,map_smul]

theorem norm_weighted_sub_le (a : Coefficient (N := N) (F := F) (P := P) K)
    (α : ℝ) (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    ‖multiply α T (apply a U-apply a V)‖ ≤ (K : ℝ) * ‖multiply α T (U-V)‖ := by
  rw [← apply_sub,multiply_apply]
  exact norm_apply_le a _

end SphericalAging.PredictableLinearCoefficient
