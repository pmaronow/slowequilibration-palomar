module

public import SphericalAging.RadialUniqueness
public import SphericalAging.PhysicalUniqueness

public section

/-! Genuine mean-square uniqueness for a bounded zero-initial finite-vector
SDE. The energy estimate uses the actual full-filtration vector Itô isometry;
no uniqueness or integral representation is supplied as an axiom. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.VectorZeroUniqueness
open HardSphereDynamics PredictableDriftTime RadialUniqueness
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma coordinate_adapted (Z : ℝ≥0 → Ω → State N) (hZa : StronglyAdapted F Z) (i : Fin N) :
    StronglyAdapted F (fun t ω => Z t ω i) :=
  fun t => (CutoffSDE.coordinate_lipschitz i).continuous.comp_stronglyMeasurable (hZa t)

lemma coordinate_continuous (Z : ℝ≥0 → Ω → State N)
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) (i : Fin N) :
    ∀ᵐ ω ∂P, Continuous (fun t => Z t ω i) :=
  hZc.mono (fun _ hc => (CutoffSDE.coordinate_lipschitz i).continuous.comp hc)

lemma coordinate_bound (Z : ℝ≥0 → Ω → State N) (L : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L) (i : Fin N) :
    ∀ᵐ ω ∂P, ∀ t, ‖Z t ω i‖ ≤ L :=
  hbound.mono (fun _ h t => (PiLp.norm_apply_le _ i).trans (h t))

@[expose] def meanSquareVector (Z : ℝ≥0 → Ω → State N) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin N, meanSquare (P := P) (fun s ω => Z s ω i) t

@[expose] def energyVector (Z : ℝ≥0 → Ω → State N) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin N, energy (P := P) (fun s ω => Z s ω i) t

lemma meanSquareVector_nonneg (Z : ℝ≥0 → Ω → State N) (t : ℝ≥0) :
    0 ≤ meanSquareVector (P := P) Z t :=
  Finset.sum_nonneg (fun _ _ => meanSquare_nonneg _ _)

lemma energyVector_nonneg (Z : ℝ≥0 → Ω → State N) (t : ℝ≥0) :
    0 ≤ energyVector (P := P) Z t :=
  Finset.sum_nonneg (fun _ _ => energy_nonneg _ _)

lemma meanSquareVector_continuous (Z : ℝ≥0 → Ω → State N) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) (L : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L) :
    Continuous (meanSquareVector (P := P) Z) := by
  apply continuous_finsetSum
  intro i _
  exact meanSquare_continuous _ (coordinate_adapted Z hZa i)
    (coordinate_continuous Z hZc i) L (coordinate_bound Z L hbound i)

lemma integral_sum_timeCut (Z : ℝ≥0 → Ω → State N) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) (L : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L) (t : ℝ≥0) :
    (∫ q, ∑ i : Fin N, FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => Z s ω i) t q ^ 2 ∂nonnegativeLebesgueMeasure.prod P) =
      energyVector (P := P) Z t := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_sq_timeCut _ (coordinate_adapted Z hZa i)
      (coordinate_continuous Z hZc i) L (coordinate_bound Z L hbound i) t)
  · intro i _
    exact (timeCut_memLp _ (coordinate_adapted Z hZa i) (coordinate_continuous Z hZc i)
      L (coordinate_bound Z L hbound i) t).integrable_sq

/-- A coefficient controlled by the state norm is controlled by the genuine
sum of coordinate energies after restriction to the current time. -/
theorem restricted_norm_sq_le_energyVector (Z : ℝ≥0 → Ω → State N)
    (hZa : StronglyAdapted F Z) (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (L M : ℝ≥0) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L)
    (T t : ℝ≥0) (ht : t ≤ T) (U : PredictableProcessL2 F P)
    (hU : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖) :
    ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U‖^2 ≤ (M : ℝ)^2 * energyVector (P := P) Z t := by
  rw [predictable_norm_sq, ← integral_sum_timeCut Z hZa hZc L hbound t,
    ← integral_const_mul]
  apply integral_mono_ae (Lp.memLp (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U : TimeProcessL2 P)).integrable_sq
    ((integrable_finsetSum _ (fun i _ =>
      (timeCut_memLp _ (coordinate_adapted Z hZa i) (coordinate_continuous Z hZc i)
        L (coordinate_bound Z L hbound i) t).integrable_sq)).const_mul _)
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t U, hU] with q hq hUq
  by_cases hqt : q.1 ∈ Ioc 0 t
  · have hb := hUq ⟨hqt.1, hqt.2.trans ht⟩
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg M.coe_nonneg (norm_nonneg _))).2 hb
    simp only [hq, FourPapersCommon.FilteredBrownian.predictableTimeFrame, mem_prod, mem_univ, and_true, hqt,
      indicator_of_mem, FourPapersCommon.continuousAdaptedTimeCut, ite_eq_left]
    rw [coordinate_square_sum, real_inner_self_eq_norm_sq]
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hs
  · simp [hq, FourPapersCommon.FilteredBrownian.predictableTimeFrame, hqt, FourPapersCommon.continuousAdaptedTimeCut]

lemma coordinate_equation_energy (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → State N) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) (L M K : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L) (T : ℝ≥0)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P) (i : Fin N)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖)
    (hU : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖)
    (heq : ∀ t, t ≤ T → ∀ᵐ ω ∂P, Z t ω i = driftVersion A t t ω +
      (VectorIto.vectorProcessLp D U t : Ω → ℝ) ω) (t : ℝ≥0) (ht : t ≤ T) :
    meanSquare (P := P) (fun s ω => Z s ω i) t ≤
      (2 * (T : ℝ) * (M : ℝ)^2 + 2 * N * (K : ℝ)^2) * energyVector (P := P) Z t := by
  have hAenergy := restricted_norm_sq_le_energyVector Z hZa hZc L M hbound T t ht A hA
  have hnoise : (∫ ω, (VectorIto.vectorProcessLp D U t : Ω → ℝ) ω ^ 2 ∂P) ≤
      (N : ℝ) * (K : ℝ)^2 * energyVector (P := P) Z t := by
    rw [PredictableItoTime.integral_sq_toLp _ (Lp.memLp _), Lp.toLp_coeFn,
      VectorIto.vectorProcessLp_norm_sq]
    calc
      _ ≤ ∑ j : Fin N, (K : ℝ)^2 * energyVector (P := P) Z t :=
        Finset.sum_le_sum (fun j _ =>
          restricted_norm_sq_le_energyVector Z hZa hZc L K hbound T t ht (U j) (hU j))
      _ = _ := by simp; ring
  have hbasic : meanSquare (P := P) (fun s ω => Z s ω i) t ≤
      2 * (∫ ω, driftVersion A t t ω ^ 2 ∂P) +
      2 * (∫ ω, (VectorIto.vectorProcessLp D U t : Ω → ℝ) ω ^ 2 ∂P) := by
    calc
      _ ≤ ∫ ω, 2 * driftVersion A t t ω ^ 2 +
          2 * (VectorIto.vectorProcessLp D U t : Ω → ℝ) ω ^ 2 ∂P := by
        apply integral_mono_ae (bounded_memLp _ (coordinate_adapted Z hZa i) L
            (coordinate_bound Z L hbound i) t).integrable_sq
          (((driftVersion_memLp A t t).integrable_sq.const_mul 2).add
            ((Lp.memLp (VectorIto.vectorProcessLp D U t)).integrable_sq.const_mul 2))
        filter_upwards [heq t ht] with ω hω
        dsimp only [Pi.add_apply]
        rw [hω]
        nlinarith [sq_nonneg (driftVersion A t t ω -
          (VectorIto.vectorProcessLp D U t : Ω → ℝ) ω)]
      _ = _ := by rw [integral_add, integral_const_mul, integral_const_mul]
                  · exact (driftVersion_memLp A t t).integrable_sq.const_mul 2
                  · exact (Lp.memLp (VectorIto.vectorProcessLp D U t)).integrable_sq.const_mul 2
  have hd : (∫ ω, driftVersion A t t ω ^ 2 ∂P) ≤
      (T : ℝ) * (M : ℝ)^2 * energyVector (P := P) Z t := by
    calc
      _ ≤ (t : ℝ) * ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := integral_sq_driftVersion_le A t
      _ ≤ (t : ℝ) * ((M : ℝ)^2 * energyVector (P := P) Z t) :=
        mul_le_mul_of_nonneg_left hAenergy t.coe_nonneg
      _ ≤ (T : ℝ) * ((M : ℝ)^2 * energyVector (P := P) Z t) :=
        mul_le_mul_of_nonneg_right (show (t : ℝ) ≤ T from ht)
          (mul_nonneg (sq_nonneg _) (energyVector_nonneg Z t))
      _ = _ := by ring
  nlinarith

lemma energyVector_eq_real_integral (Z : ℝ≥0 → Ω → State N) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) (L : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L) (t : ℝ≥0) :
    energyVector (P := P) Z t = ∫ s in (0 : ℝ)..(t : ℝ),
      meanSquareVector (P := P) Z s.toNNReal := by
  unfold energyVector meanSquareVector
  simp only [energy_eq_real_integral]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ((meanSquare_continuous _ (coordinate_adapted Z hZa i)
    (coordinate_continuous Z hZc i) L (coordinate_bound Z L hbound i)).comp
      continuous_real_toNNReal).intervalIntegrable _ _

/-- Genuine bounded vector SDE uniqueness from the actual drift primitives,
full-filtration Itô integrals, and linear coefficient bounds. -/
theorem bounded_vector_equation_zero (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → State N) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) (L M K : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ L) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (hA : ∀ i, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A i : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖)
    (hU : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U i j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖)
    (heq : ∀ t, t ≤ T → ∀ i, ∀ᵐ ω ∂P, Z t ω i = driftVersion (A i) t t ω +
      (VectorIto.vectorProcessLp D (U i) t : Ω → ℝ) ω) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → Z t ω = 0 := by
  let f : ℝ → ℝ := fun x => meanSquareVector (P := P) Z x.toNNReal
  have hfc : Continuous f := (meanSquareVector_continuous Z hZa hZc L hbound).comp
    continuous_real_toNNReal
  have hfzero : ∀ x ∈ Icc 0 (T : ℝ), f x = 0 := by
    apply continuous_integral_gronwall_zero f hfc (fun x => meanSquareVector_nonneg Z _)
      T (N * (2 * (T : ℝ) * (M : ℝ)^2 + 2 * N * (K : ℝ)^2))
    intro x hx
    have hxt : x.toNNReal ≤ T := by
      simpa only [Real.toNNReal_coe] using (Real.toNNReal_le_toNNReal hx.2)
    have hi : meanSquareVector (P := P) Z x.toNNReal ≤
        (N : ℝ) * (2 * (T : ℝ) * (M : ℝ)^2 + 2 * N * (K : ℝ)^2) *
          energyVector (P := P) Z x.toNNReal := by
      calc
        _ ≤ ∑ i : Fin N, (2 * (T : ℝ) * (M : ℝ)^2 + 2 * N * (K : ℝ)^2) *
            energyVector (P := P) Z x.toNNReal :=
          Finset.sum_le_sum (fun i _ => coordinate_equation_energy D Z hZa hZc L M K
            hbound T (A i) (U i) i (hA i) (hU i) (fun t ht => heq t ht i) _ hxt)
        _ = _ := by simp; ring
    rw [energyVector_eq_real_integral Z hZa hZc L hbound,
      Real.coe_toNNReal _ hx.1] at hi
    exact hi
  have hfixed : ∀ i : Fin N, ∀ t, t ≤ T →
      (fun ω => Z t ω i) =ᵐ[P] (fun _ => (0 : ℝ)) := by
    intro i t ht
    have hmean : meanSquareVector (P := P) Z t = 0 := by
      simpa only [f, Real.toNNReal_coe] using hfzero t ⟨t.coe_nonneg, ht⟩
    have hle : meanSquare (P := P) (fun s ω => Z s ω i) t ≤ meanSquareVector (P := P) Z t := by
      apply Finset.single_le_sum (f := fun j : Fin N => meanSquare (P := P) (fun s ω => Z s ω j) t)
      · intro j _; exact meanSquare_nonneg _ _
      · exact Finset.mem_univ i
    have hmi : meanSquare (P := P) (fun s ω => Z s ω i) t = 0 := by
      rw [hmean] at hle
      exact le_antisymm hle (meanSquare_nonneg _ _)
    have hsq : (fun ω => Z t ω i ^ 2) =ᵐ[P] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
        (bounded_memLp _ (coordinate_adapted Z hZa i) L
          (coordinate_bound Z L hbound i) t).integrable_sq).mp hmi
    filter_upwards [hsq] with ω hω
    exact sq_eq_zero_iff.mp hω
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin N, ∀ t, t ≤ T → Z t ω i = 0 := by
    apply ae_all_iff.mpr
    intro i
    have hc : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => Z (min t T) ω i) :=
      (coordinate_continuous Z hZc i).mono (fun _ h =>
        h.comp (continuous_id.min continuous_const))
    have hz := PredictableItoTime.continuous_processes_ae_eq_of_fixedTime hc
      (P := P) (.of_forall (fun _ => continuous_const))
      (fun t => hfixed i (min t T) (min_le_right _ _))
    filter_upwards [hz] with ω hω
    intro t ht
    simpa only [min_eq_left ht] using hω t
  filter_upwards [hall] with ω hω
  intro t ht
  exact PiLp.ext (fun i => hω i t ht)

end SphericalAging.VectorZeroUniqueness
