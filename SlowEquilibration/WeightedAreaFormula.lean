-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ext

/-!
# The nonnegative weighted equal-dimensional area formula

The multiplicity is the actual ENNReal sum over the fiber, with no bound on its
size. Regular points are partitioned into countably many measurable injective
pieces obtained from the inverse function theorem. Mathlib's injective Jacobian
formula applies on each piece, while equal-dimensional Sard removes the critical
values. This is the argument of Lemma `kr-area` in the manuscript.
-/

@[expose] public section

namespace SlowEquilibration.WeightedAreaFormula

open Set MeasureTheory MeasureTheory.Measure Filter Function
open scoped ENNReal Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- The genuine nonnegative sum over all points in a fiber. -/
def fiberSum (f : E → E) (s : Set E) (w : E → ℝ≥0∞) (y : E) : ℝ≥0∞ :=
  ∑' z : {x : E | x ∈ s ∧ f x = y}, w z

/-- Regular points of the map in the open domain. -/
def regularSet (f : E → E) (s : Set E) : Set E :=
  {x | x ∈ s ∧ (fderiv ℝ f x).det ≠ 0}

/-- Critical points in the open domain. -/
def criticalSet (f : E → E) (s : Set E) : Set E :=
  {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] in
lemma regularSet_subset (f : E → E) (s : Set E) : regularSet f s ⊆ s := fun _ h => h.1

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] in
lemma regularSet_isOpen (f : E → E) (s : Set E) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) : IsOpen (regularSet f s) := by
  have hc : ContinuousOn (fun x => (fderiv ℝ f x).det) s :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hs (by norm_num))
  exact hc.isOpen_inter_preimage hs isOpen_ne

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Sard's null critical-value statement uses actual Frechet derivatives. -/
theorem critical_values_null (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (s : Set E) (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) :
    μ (f '' criticalSet f s) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
  · intro x hx
    exact ((hf.contDiffAt (hs.mem_nhds hx.1)).differentiableAt_one.hasFDerivAt).hasFDerivWithinAt
  · intro x hx
    exact hx.2

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- Every regular point has an injective open neighborhood in the regular set. -/
lemma regular_inverse_neighborhood (f : E → E) (s : Set E) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) (a : E) (ha : a ∈ regularSet f s) :
    ∃ u : Set E, IsOpen u ∧ a ∈ u ∧ u ⊆ regularSet f s ∧ InjOn f u := by
  let e : E ≃L[ℝ] E :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr ha.2)).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = fderiv ℝ f a := by
    ext z
    exact LinearMap.equivOfIsUnitDet_apply _ z
  have hc := hf.contDiffAt (hs.mem_nhds ha.1)
  have hd : HasFDerivAt f (e : E →L[ℝ] E) a := by
    rw [he]
    exact hc.differentiableAt_one.hasFDerivAt
  let H := hc.toOpenPartialHomeomorph f hd (by norm_num)
  refine ⟨regularSet f s ∩ H.source, (regularSet_isOpen f s hs hf).inter H.open_source,
    ⟨ha, hc.mem_toOpenPartialHomeomorph_source hd (by norm_num)⟩, inter_subset_left, ?_⟩
  simpa [H] using H.injOn.mono (show regularSet f s ∩ H.source ⊆ H.source from inter_subset_right)

/-- A countable measurable injective partition of the complete regular set. -/
theorem regular_injective_partition (f : E → E) (s : Set E) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) :
    ∃ p : ℕ → Set E,
      (∀ i, MeasurableSet (p i)) ∧ Pairwise (fun i j => Disjoint (p i) (p j)) ∧
      (⋃ i, p i) = regularSet f s ∧ (∀ i, p i ⊆ regularSet f s) ∧
      (∀ i, InjOn f (p i)) := by
  classical
  by_cases hempty : (regularSet f s).Nonempty
  · choose u huOpen hua huSub huInj using
      (fun a : regularSet f s => regular_inverse_neighborhood f s hs hf a a.2)
    have hcover : (⋃ a : regularSet f s, u a) = regularSet f s := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, hz⟩ := mem_iUnion.mp hz
        exact huSub a hz
      · intro hz
        exact mem_iUnion.mpr ⟨⟨z, hz⟩, hua ⟨z, hz⟩⟩
    obtain ⟨T, hT, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable u huOpen
    have hTne : T.Nonempty := by
      obtain ⟨z, hz⟩ := hempty
      have hzU : z ∈ ⋃ a ∈ T, u a := by rw [hTu, hcover]; exact hz
      obtain ⟨a, ha, _⟩ := mem_iUnion₂.mp hzU
      exact ⟨a, ha⟩
    obtain ⟨v, hv⟩ := hT.exists_eq_range hTne
    let U : ℕ → Set E := fun n => u (v n)
    have hUc : (⋃ n, U n) = regularSet f s := by
      change (⋃ n, u (v n)) = regularSet f s
      rw [← biUnion_range, ← hv, hTu, hcover]
    refine ⟨disjointed U, MeasurableSet.disjointed (fun n => (huOpen (v n)).measurableSet),
      disjoint_disjointed U, ?_, ?_, ?_⟩
    · rw [iUnion_disjointed, hUc]
    · intro i
      exact (disjointed_subset U i).trans (huSub (v i))
    · intro i
      exact (huInj (v i)).mono (disjointed_subset U i)
  · have he : regularSet f s = ∅ := not_nonempty_iff_eq_empty.mp hempty
    refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, ?_, ?_, fun _ => empty_subset _,
      fun _ => injOn_empty f⟩
    · intro i j hij
      simp
    · simp [he]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- On one injective piece, fiber sums are the measurable inverse-branch weight. -/
lemma fiberSum_injective_extend (f : E → E) (s : Set E) (w : E → ℝ≥0∞)
    (hf : InjOn f s) (y : E) :
    fiberSum f s w y = Function.extend (s.domRestrict f) (fun x : s => w x) (fun _ => 0) y := by
  classical
  by_cases hy : y ∈ f '' s
  · obtain ⟨a, ha, hfa⟩ := hy
    let z : {x : E | x ∈ s ∧ f x = y} := ⟨a, ha, hfa⟩
    have hz : ∀ q : {x : E | x ∈ s ∧ f x = y}, q = z := by
      intro q
      apply Subtype.ext
      exact hf q.2.1 ha (q.2.2.trans hfa.symm)
    have hs : fiberSum f s w y = w a := by
      unfold fiberSum
      exact tsum_eq_single z fun q hq => (hq (hz q)).elim
    rw [hs, ← hfa]
    exact ((injOn_iff_injective.mp hf).extend_apply (fun x : s => w x) (fun _ => 0) ⟨a, ha⟩).symm
  · have hzero : fiberSum f s w y = 0 := by
      unfold fiberSum
      apply ENNReal.tsum_eq_zero.mpr
      intro q
      exact (hy ⟨q, q.2.1, q.2.2⟩).elim
    have hno : ¬∃ a : s, s.domRestrict f a = y := by
      rintro ⟨a, ha⟩
      exact hy ⟨a, a.2, ha⟩
    rw [hzero, Function.extend_apply' (fun x : s => w x) (fun _ : E => 0) y hno]

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma fiberSum_injective_measurable (f : E → E) (s : Set E) (w : E → ℝ≥0∞)
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x)
    (hi : InjOn f s) (hw : Measurable fun x : s => w x) :
    Measurable (fiberSum f s w) := by
  have he := MeasureTheory.measurableEmbedding_of_fderivWithin hs hd hi
  have hm := he.measurable_extend hw (measurable_const : Measurable (fun _ : E => (0 : ℝ≥0∞)))
  convert hm using 1
  ext y
  exact fiberSum_injective_extend f s w hi y

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma fiberSum_partition (f : E → E) (s : Set E) (w : E → ℝ≥0∞)
    (p : ℕ → Set E) (hd : Pairwise (fun i j => Disjoint (p i) (p j)))
    (hp : (⋃ i, p i) = s) (y : E) :
    fiberSum f s w y = ∑' i, fiberSum f (p i) w y := by
  classical
  have hset : {x : E | x ∈ s ∧ f x = y} = ⋃ i, {x : E | x ∈ p i ∧ f x = y} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    rw [← hp]
    simp only [mem_iUnion, exists_and_right]
  have hdis : Set.univ.PairwiseDisjoint (fun i : ℕ => {x : E | x ∈ p i ∧ f x = y}) := by
    intro i _ j _ hij
    exact (hd hij).mono (fun _ h => h.1) (fun _ h => h.1)
  unfold fiberSum
  rw [hset, ENNReal.tsum_biUnion hdis]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma fiberSum_eq_zero_of_not_mem_image (f : E → E) (s : Set E) (w : E → ℝ≥0∞)
    (y : E) (hy : y ∉ f '' s) : fiberSum f s w y = 0 := by
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro q
  exact (hy ⟨q, q.2.1, q.2.2⟩).elim

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma fiberSum_injective_apply (f : E → E) (s : Set E) (w : E → ℝ≥0∞)
    (hi : InjOn f s) (x : E) (hx : x ∈ s) : fiberSum f s w (f x) = w x := by
  rw [fiberSum_injective_extend f s w hi]
  exact (injOn_iff_injective.mp hi).extend_apply (fun z : s => w z) (fun _ => 0) ⟨x, hx⟩

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- The weighted area formula on one measurable injective piece. -/
lemma injective_weighted_area (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (s : Set E) (w : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x) (hi : InjOn f s) :
    (∫⁻ y, fiberSum f s w y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
  have hsupport : Function.support (fiberSum f s w) ⊆ f '' s := by
    intro y hy
    by_contra h
    exact hy (fiberSum_eq_zero_of_not_mem_image f s w y h)
  calc
    (∫⁻ y, fiberSum f s w y ∂μ) = ∫⁻ y in f '' s, fiberSum f s w y ∂μ :=
      (setLIntegral_eq_of_support_subset hsupport).symm
    _ = ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * fiberSum f s w (f x) ∂μ :=
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hd hi _
    _ = ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
      apply setLIntegral_congr_fun hs
      intro x hx
      dsimp only
      rw [fiberSum_injective_apply f s w hi x hx]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] in
lemma fiberSet_eq_regular (f : E → E) (s : Set E) (y : E)
    (hy : y ∉ f '' criticalSet f s) :
    {x : E | x ∈ s ∧ f x = y} = {x : E | x ∈ regularSet f s ∧ f x = y} := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨hx.1, ?_⟩, hx.2⟩
    intro hdet
    exact hy ⟨x, ⟨hx.1, hdet⟩, hx.2⟩
  · intro hx
    exact ⟨hx.1.1, hx.2⟩

/-- The actual weighted C1 area formula. The weight need only be Borel on the
open domain; both sides are genuine nonnegative Lebesgue integrals and may be
infinite. The full fiber sum is almost everywhere measurable, including when
it is left arbitrary on the null critical-value set. -/
theorem weighted_area_formula (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (s : Set E) (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (w : E → ℝ≥0∞) (hw : Measurable fun x : s => w x) :
    AEMeasurable (fiberSum f s w) μ ∧
      (∫⁻ y, fiberSum f s w y ∂μ) =
        ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
  classical
  obtain ⟨p, hpMeas, hpDisj, hpUnion, hpSub, hpInj⟩ := regular_injective_partition f s hs hf
  have hpDer : ∀ i x, x ∈ p i → HasFDerivWithinAt f (fderiv ℝ f x) (p i) x := by
    intro i x hx
    exact ((hf.contDiffAt (hs.mem_nhds (hpSub i hx).1)).differentiableAt_one.hasFDerivAt).hasFDerivWithinAt
  have hpWeight : ∀ i, Measurable fun x : p i => w x := by
    intro i
    have hinc : Measurable (fun x : p i => (⟨(x : E), (hpSub i x.2).1⟩ : s)) :=
      measurable_subtype_coe.subtype_mk
    exact hw.comp hinc
  have hpCountMeas : ∀ i, Measurable (fiberSum f (p i) w) := fun i =>
    fiberSum_injective_measurable f (p i) w (hpMeas i) (hpDer i) (hpInj i) (hpWeight i)
  have hregFun : fiberSum f (regularSet f s) w = fun y => ∑' i, fiberSum f (p i) w y :=
    funext fun y => fiberSum_partition f (regularSet f s) w p hpDisj hpUnion y
  have hregMeas : Measurable (fiberSum f (regularSet f s) w) := by
    rw [hregFun]
    exact Measurable.tsum hpCountMeas
  have hnull := critical_values_null μ f s hs hf
  have hnot : ∀ᵐ y ∂μ, y ∉ f '' criticalSet f s := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  have hae : fiberSum f s w =ᵐ[μ] fiberSum f (regularSet f s) w := by
    filter_upwards [hnot] with y hy
    unfold fiberSum
    rw [fiberSet_eq_regular f s y hy]
  have hregIntegral : (∫⁻ y, fiberSum f (regularSet f s) w y ∂μ) =
      ∫⁻ x in regularSet f s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
    calc
      (∫⁻ y, fiberSum f (regularSet f s) w y ∂μ) =
          ∫⁻ y, ∑' i, fiberSum f (p i) w y ∂μ := by rw [hregFun]
      _ = ∑' i, ∫⁻ y, fiberSum f (p i) w y ∂μ :=
        lintegral_tsum (fun i => (hpCountMeas i).aemeasurable)
      _ = ∑' i, ∫⁻ x in p i, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
        apply tsum_congr
        intro i
        exact injective_weighted_area μ f (p i) w (hpMeas i) (hpDer i) (hpInj i)
      _ = ∫⁻ x in regularSet f s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
        rw [← hpUnion]
        exact (lintegral_iUnion hpMeas hpDisj _).symm
  have hregOpen := regularSet_isOpen f s hs hf
  have hzero : (∫⁻ x in s \ regularSet f s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ) = 0 := by
    apply setLIntegral_eq_zero (hs.measurableSet.diff hregOpen.measurableSet)
    intro x hx
    have hd : (fderiv ℝ f x).det = 0 := by
      by_contra hd
      exact hx.2 ⟨hx.1, hd⟩
    simp [hd]
  have hright := lintegral_inter_add_sdiff (μ := μ)
    (fun x => ENNReal.ofReal |(fderiv ℝ f x).det| * w x) s hregOpen.measurableSet
  rw [inter_eq_right.mpr (regularSet_subset f s), hzero, add_zero] at hright
  refine ⟨hregMeas.aemeasurable.congr hae.symm, ?_⟩
  exact (lintegral_congr_ae hae).trans (hregIntegral.trans hright)


/-- The regular-fiber counting function is Borel, with a possibly infinite value. -/
theorem regular_fiberSum_measurable (f : E → E) (s : Set E) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) (w : E → ℝ≥0∞) (hw : Measurable fun x : s => w x) :
    Measurable (fiberSum f (regularSet f s) w) := by
  classical
  obtain ⟨p, hpMeas, hpDisj, hpUnion, hpSub, hpInj⟩ := regular_injective_partition f s hs hf
  have hpDer : ∀ i x, x ∈ p i → HasFDerivWithinAt f (fderiv ℝ f x) (p i) x := by
    intro i x hx
    exact ((hf.contDiffAt (hs.mem_nhds (hpSub i hx).1)).differentiableAt_one.hasFDerivAt).hasFDerivWithinAt
  have hpWeight : ∀ i, Measurable fun x : p i => w x := by
    intro i
    have hinc : Measurable (fun x : p i => (⟨(x : E), (hpSub i x.2).1⟩ : s)) :=
      measurable_subtype_coe.subtype_mk
    exact hw.comp hinc
  have hpCount : ∀ i, Measurable (fiberSum f (p i) w) := fun i =>
    fiberSum_injective_measurable f (p i) w (hpMeas i) (hpDer i) (hpInj i) (hpWeight i)
  have hfun : fiberSum f (regularSet f s) w = fun y => ∑' i, fiberSum f (p i) w y :=
    funext fun y => fiberSum_partition f (regularSet f s) w p hpDisj hpUnion y
  rw [hfun]
  exact Measurable.tsum hpCount

/-- Away from critical values, the full fiber-sum function is Borel. -/
theorem regular_values_fiberSum_measurable (f : E → E) (s : Set E) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) (w : E → ℝ≥0∞) (hw : Measurable fun x : s => w x) :
    Measurable (fun y : {y : E | y ∉ f '' criticalSet f s} => fiberSum f s w y) := by
  have hm : Measurable (fun y : {y : E | y ∉ f '' criticalSet f s} =>
      fiberSum f (regularSet f s) w y) :=
    (regular_fiberSum_measurable f s hs hf w hw).comp measurable_subtype_coe
  convert hm using 1
  funext y
  unfold fiberSum
  rw [fiberSet_eq_regular f s y y.2]

/-- Every regular-value fiber is countable; the sum is therefore the ordinary
countable nonnegative sum, without requiring a finite multiplicity bound. -/
theorem regular_value_fiber_countable (f : E → E) (s : Set E) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) (y : E) (hy : y ∉ f '' criticalSet f s) :
    {x : E | x ∈ s ∧ f x = y}.Countable := by
  classical
  obtain ⟨p, _, _, hpUnion, _, hpInj⟩ := regular_injective_partition f s hs hf
  have hpiece : ∀ i, {x : E | x ∈ p i ∧ f x = y}.Subsingleton := by
    intro i a ha b hb
    exact hpInj i ha.1 hb.1 (ha.2.trans hb.2.symm)
  have hset : {x : E | x ∈ regularSet f s ∧ f x = y} = ⋃ i, {x : E | x ∈ p i ∧ f x = y} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    rw [← hpUnion]
    simp only [mem_iUnion, exists_and_right]
  rw [fiberSet_eq_regular f s y hy, hset]
  exact countable_iUnion fun i => (hpiece i).countable

/-- Changing the counting sum arbitrarily on critical values leaves the area
identity unchanged, exactly as allowed in Lemma `kr-area`. -/
theorem weighted_area_formula_null_modification (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (s : Set E) (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (w : E → ℝ≥0∞) (hw : Measurable fun x : s => w x)
    (g : E → ℝ≥0∞) (hg : ∀ y ∉ f '' criticalSet f s, g y = fiberSum f s w y) :
    AEMeasurable g μ ∧ (∫⁻ y, g y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x ∂μ := by
  obtain ⟨hm, harea⟩ := weighted_area_formula μ f s hs hf w hw
  have hnot : ∀ᵐ y ∂μ, y ∉ f '' criticalSet f s := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using critical_values_null μ f s hs hf
  have heq : g =ᵐ[μ] fiberSum f s w := hnot.mono fun y hy => hg y hy
  exact ⟨hm.congr heq.symm, (lintegral_congr_ae heq).trans harea⟩

/-- The manuscript's literal Euclidean/Lebesgue specialization. -/
theorem euclidean_weighted_area_formula (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (w : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hw : Measurable fun x : s => w x) :
    volume (f '' criticalSet f s) = 0 ∧ AEMeasurable (fiberSum f s w) volume ∧
      (∫⁻ y, fiberSum f s w y) = ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| * w x :=
  ⟨critical_values_null volume f s hs hf, weighted_area_formula volume f s hs hf w hw⟩


end
end SlowEquilibration.WeightedAreaFormula
