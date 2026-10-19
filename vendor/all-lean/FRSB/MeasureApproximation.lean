module
public import FRSB.ParisiMeasureTopology
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! # Finite atomic approximation preserving a prescribed finite set

A grid index and the comparisons with every prescribed point form a finite
measurable partition. Choosing one point from each nonempty partition cell
gives an actual finite-range map. Points in the same cell have distance at
most one grid mesh, and their left-cut and singleton membership agree at
every prescribed point. This construction does not move nearby mass onto
one of the prescribed atoms.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open scoped Classical

namespace FRSB
open Paper

/-- A finite measurable classifier, retaining both left and point membership. -/
abbrev PreservingSignature (S : Finset Overlap) (n : ℕ) :=
  Fin (n + 2) × (S → Bool × Bool)

def preservingSignature (S : Finset Overlap) (n : ℕ) (q : Overlap) :
    PreservingSignature S n :=
  (parisiGridIndex n q, fun s => (decide (q < s.val), decide (q = s.val)))

theorem measurable_preservingSignature (S : Finset Overlap) (n : ℕ) :
    Measurable (preservingSignature S n) := by
  have hindex : Measurable (parisiGridIndex n) := by
    apply measurable_to_countable'
    intro i
    have he : parisiGridIndex n ⁻¹' {i} =
        (fun q : Overlap => Nat.ceil ((n + 1 : ℕ) * (q : ℝ))) ⁻¹' {i.val} := by
      ext q
      simp only [mem_preimage, mem_singleton_iff, Fin.ext_iff, parisiGridIndex]
    rw [he]
    exact ((measurable_const.mul measurable_subtype_coe).nat_ceil)
      (measurableSet_singleton i.val)
  apply hindex.prodMk
  apply Measurable.of_eval
  intro s
  have hlt : Measurable (fun q : Overlap => decide (q < s.val)) := by
    apply measurable_to_bool
    have he : (fun q : Overlap => decide (q < s.val)) ⁻¹' {true} = Iio s.val := by
      ext q
      simp
    rw [he]
    exact isOpen_Iio.measurableSet
  have heq : Measurable (fun q : Overlap => decide (q = s.val)) := by
    apply measurable_to_bool
    have he : (fun q : Overlap => decide (q = s.val)) ⁻¹' {true} = {s.val} := by
      ext q
      simp
    rw [he]
    exact measurableSet_singleton _
  exact hlt.prodMk heq

/-- Pick a representative of each nonempty cell; empty cells use zero. -/
def preservingRepresentative (S : Finset Overlap) (n : ℕ)
    (a : PreservingSignature S n) : Overlap :=
  if h : ∃ q, preservingSignature S n q = a then Classical.choose h
  else ⟨0, by constructor <;> norm_num⟩

theorem preservingRepresentative_spec (S : Finset Overlap) (n : ℕ)
    (a : PreservingSignature S n) (ha : ∃ q, preservingSignature S n q = a) :
    preservingSignature S n (preservingRepresentative S n a) = a := by
  simp only [preservingRepresentative, dite_eq_left ha]
  exact Classical.choose_spec ha

/-- The actual finite-range overlap quantizer preserving all points in `S`. -/
def preservingRound (S : Finset Overlap) (n : ℕ) (q : Overlap) : Overlap :=
  preservingRepresentative S n (preservingSignature S n q)

theorem measurable_preservingRound (S : Finset Overlap) (n : ℕ) :
    Measurable (preservingRound S n) :=
  (measurable_of_countable (preservingRepresentative S n)).comp
    (measurable_preservingSignature S n)

theorem preservingSignature_round (S : Finset Overlap) (n : ℕ) (q : Overlap) :
    preservingSignature S n (preservingRound S n q) = preservingSignature S n q :=
  preservingRepresentative_spec S n _ ⟨q, rfl⟩

theorem preservingRound_gridIndex (S : Finset Overlap) (n : ℕ) (q : Overlap) :
    parisiGridIndex n (preservingRound S n q) = parisiGridIndex n q :=
  congrArg Prod.fst (preservingSignature_round S n q)

theorem preservingRound_lt_iff (S : Finset Overlap) (n : ℕ) (q s : Overlap)
    (hs : s ∈ S) : preservingRound S n q < s ↔ q < s := by
  have he := congrArg (fun a : PreservingSignature S n => (a.2 ⟨s, hs⟩).1)
    (preservingSignature_round S n q)
  simpa [preservingSignature] using he

theorem preservingRound_eq_iff (S : Finset Overlap) (n : ℕ) (q s : Overlap)
    (hs : s ∈ S) : preservingRound S n q = s ↔ q = s := by
  have he := congrArg (fun a : PreservingSignature S n => (a.2 ⟨s, hs⟩).2)
    (preservingSignature_round S n q)
  simpa [preservingSignature] using he

theorem preservingRound_le_iff (S : Finset Overlap) (n : ℕ) (q s : Overlap)
    (hs : s ∈ S) : preservingRound S n q ≤ s ↔ q ≤ s := by
  simp only [le_iff_lt_or_eq, preservingRound_lt_iff S n q s hs,
    preservingRound_eq_iff S n q s hs]

theorem preservingRound_gt_iff (S : Finset Overlap) (n : ℕ) (q s : Overlap)
    (hs : s ∈ S) : s < preservingRound S n q ↔ s < q := by
  simp only [lt_iff_not_ge, preservingRound_le_iff S n q s hs]

theorem preservingRound_fixed (S : Finset Overlap) (n : ℕ) (s : Overlap)
    (hs : s ∈ S) : preservingRound S n s = s :=
  (preservingRound_eq_iff S n s s hs).mpr rfl

theorem abs_preservingRound_sub_le_mesh (S : Finset Overlap) (n : ℕ) (q : Overlap) :
    |(preservingRound S n q : ℝ) - (q : ℝ)| ≤ 1 / (n + 1 : ℕ) := by
  have hgrid : parisiGridRound n (preservingRound S n q) = parisiGridRound n q := by
    unfold parisiGridRound
    rw [preservingRound_gridIndex]
  have hr := le_parisiGridRound n (preservingRound S n q)
  have hq := le_parisiGridRound n q
  have hdr := parisiGridRound_sub_lt_mesh n (preservingRound S n q)
  have hdq := parisiGridRound_sub_lt_mesh n q
  rw [hgrid] at hr hdr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem finite_range_preservingRound (S : Finset Overlap) (n : ℕ) :
    (Set.range (preservingRound S n)).Finite :=
  (Set.finite_range (preservingRepresentative S n)).subset (by
    rintro _ ⟨q, rfl⟩
    exact ⟨preservingSignature S n q, rfl⟩)

theorem tendsto_preservingRound (S : Finset Overlap) (q : Overlap) :
    Tendsto (fun n => preservingRound S n q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  have hlim : Tendsto (fun n : ℕ => (preservingRound S n q : ℝ) - (q : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by
      simpa only [Real.norm_eq_abs] using abs_preservingRound_sub_le_mesh S n q)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_add_cancel, zero_add] using hlim.add_const (q : ℝ)

/-- The concrete finitely supported probability law of the quantizer. -/
def preservingMeasure (μ : ParisiMeasure) (S : Finset Overlap) (n : ℕ) : ParisiMeasure :=
  μ.map (preservingRound S n)

theorem preservingMeasure_left_mass (μ : ParisiMeasure) (S : Finset Overlap)
    (n : ℕ) (s : Overlap) (hs : s ∈ S) :
    (preservingMeasure μ S n : Measure Overlap) (Iio s) = (μ : Measure Overlap) (Iio s) := by
  unfold preservingMeasure
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (measurable_preservingRound S n) isOpen_Iio.measurableSet]
  congr 1
  ext q
  exact preservingRound_lt_iff S n q s hs

theorem preservingMeasure_atom_mass (μ : ParisiMeasure) (S : Finset Overlap)
    (n : ℕ) (s : Overlap) (hs : s ∈ S) :
    (preservingMeasure μ S n : Measure Overlap) {s} = (μ : Measure Overlap) {s} := by
  unfold preservingMeasure
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (measurable_preservingRound S n) (measurableSet_singleton s)]
  congr 1
  ext q
  exact preservingRound_eq_iff S n q s hs

theorem preservingMeasure_cdf_mass (μ : ParisiMeasure) (S : Finset Overlap)
    (n : ℕ) (s : Overlap) (hs : s ∈ S) :
    parisiCDF (preservingMeasure μ S n) s = parisiCDF μ s := by
  unfold preservingMeasure parisiCDF
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (measurable_preservingRound S n)
    (isClosed_le continuous_subtype_val continuous_const).measurableSet]
  congr 2
  ext q
  exact preservingRound_le_iff S n q s hs

theorem preservingMeasure_open_interval_mass (μ : ParisiMeasure) (S : Finset Overlap)
    (n : ℕ) (a b : Overlap) (ha : a ∈ S) (hb : b ∈ S) :
    (preservingMeasure μ S n : Measure Overlap) (Ioo a b) =
      (μ : Measure Overlap) (Ioo a b) := by
  unfold preservingMeasure
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (measurable_preservingRound S n) isOpen_Ioo.measurableSet]
  congr 1
  ext q
  simp only [mem_preimage, mem_Ioo, preservingRound_gt_iff S n q a ha,
    preservingRound_lt_iff S n q b hb]

theorem finite_support_preservingMeasure (μ : ParisiMeasure) (S : Finset Overlap) (n : ℕ) :
    (preservingMeasure μ S n : Measure Overlap).support.Finite := by
  apply (finite_range_preservingRound S n).subset
  apply Measure.support_subset_of_isClosed
    (finite_range_preservingRound S n).isClosed
  unfold preservingMeasure
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_preservingRound S n).aemeasurable
    (finite_range_preservingRound S n).measurableSet).mpr
  exact .of_forall fun q => ⟨q, rfl⟩

/-- Actual weak convergence, tested against all bounded continuous functions. -/
theorem tendsto_preservingMeasure (μ : ParisiMeasure) (S : Finset Overlap) :
    Tendsto (preservingMeasure μ S) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have heq (n : ℕ) : (∫ q, f q ∂(preservingMeasure μ S n : Measure Overlap)) =
      ∫ q, f (preservingRound S n q) ∂(μ : Measure Overlap) := by
    unfold preservingMeasure
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map_of_stronglyMeasurable (measurable_preservingRound S n)
      f.continuous.measurable.stronglyMeasurable
  simp_rw [heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
  · exact .of_forall fun n => (f.continuous.measurable.comp
      (measurable_preservingRound S n)).aestronglyMeasurable
  · exact .of_forall fun _ => .of_forall fun _ => f.norm_coe_le_norm _
  · exact integrable_const _
  · exact .of_forall fun q => f.continuous.continuousAt.tendsto.comp
      (tendsto_preservingRound S q)

/-- Actual CDF convergence in the paper's L¹ time norm. -/
theorem tendsto_preservingMeasure_cdfDistance (μ : ParisiMeasure) (S : Finset Overlap) :
    Tendsto (fun n => parisiCDFDistance (preservingMeasure μ S n) μ) atTop (𝓝 0) :=
  tendsto_parisiCDFDistance_of_tendsto (tendsto_preservingMeasure μ S)

/-- **Lemma 2.2**, with an arbitrary finite set of physical overlap points.
The witnesses are actual probability measures with finite topological support. -/
theorem exists_preservingApproximation (μ : ParisiMeasure) (S : Set Overlap)
    (hS : S.Finite) :
    ∃ μn : ℕ → ParisiMeasure,
      (∀ n, (μn n : Measure Overlap).support.Finite) ∧
      Tendsto μn atTop (𝓝 μ) ∧
      (∀ s ∈ S, ∀ n,
        (μn n : Measure Overlap) (Iio s) = (μ : Measure Overlap) (Iio s) ∧
        (μn n : Measure Overlap) {s} = (μ : Measure Overlap) {s}) ∧
      Tendsto (fun n => parisiCDFDistance (μn n) μ) atTop (𝓝 0) := by
  refine ⟨preservingMeasure μ hS.toFinset,
    finite_support_preservingMeasure μ hS.toFinset,
    tendsto_preservingMeasure μ hS.toFinset, ?_,
    tendsto_preservingMeasure_cdfDistance μ hS.toFinset⟩
  intro s hs n
  have hsf : s ∈ hS.toFinset := hS.mem_toFinset.mpr hs
  exact ⟨preservingMeasure_left_mass μ hS.toFinset n s hsf,
    preservingMeasure_atom_mass μ hS.toFinset n s hsf⟩

/-- The unparameterized exact finite atomic approximation statement. -/
def FiniteAtomicApproximationTarget : Prop :=
  ∀ (μ : ParisiMeasure) (S : Set Overlap), S.Finite →
    ∃ μn : ℕ → ParisiMeasure,
      (∀ n, (μn n : Measure Overlap).support.Finite) ∧
      Tendsto μn atTop (𝓝 μ) ∧
      (∀ s ∈ S, ∀ n,
        (μn n : Measure Overlap) (Iio s) = (μ : Measure Overlap) (Iio s) ∧
        (μn n : Measure Overlap) {s} = (μ : Measure Overlap) {s}) ∧
      Tendsto (fun n => parisiCDFDistance (μn n) μ) atTop (𝓝 0)

theorem finite_atomic_approximation : FiniteAtomicApproximationTarget :=
  exists_preservingApproximation

end FRSB
