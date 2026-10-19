-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapturePoleNull
public import SlowEquilibration.PureCapturePhysicalDiagonalBridge
public import SlowEquilibration.SourcePureCapBorelMarkedValue
public import SlowEquilibration.SphericalLocalMaxPhysicalIntensity
public import SlowEquilibration.SourceReductionCompactBandProjection
public import SlowEquilibration.SourcePhysicalPairSelectionRegularity
public import SlowEquilibration.SphericalFiniteCritical
public import SlowEquilibration.SphericalGibbsAllDimensions

/-! Actual-set comparisons used in the pure microscopic capture proof.
The radial coarea formula removes both endpoint poles for arbitrary Borel
partition marks, and the original critical-energy windows are identified
with the literal marked Kac--Rice counts. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureCaptureBandComplementBound
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalMarkedWindows SphericalGaussianJet
open PureCapturePhysicalDiagonalBridge SourcePureCapBorelMarkedValue
open PairConditionalDeterminantMoments SphericalMorse SourcePureCapturePoleNull
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Original-field critical points in an unnormalized energy set. -/
def originalEnergyCriticalSet (d : ℕ) (μ : FiniteMixture)
    (E : Set ℝ) (J : Disorder (d+2) μ.maxDegree) : Set (Vector (d+2)) :=
  {u | ‖u‖^2 = ((d+2 : ℕ) : ℝ) ∧
    surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
    field (mixtureCoefficients μ) J u ∈ E}

/-- The literal original critical-point union of overlap intervals. -/
def originalEnergyBandUnion (d : ℕ) (μ : FiniteMixture)
    (m L q b : ℝ) (J : Disorder (d+2) μ.maxDegree) : Set (Vector (d+2)) :=
  {x | ∃ u ∈ originalEnergyCriticalSet d μ (Icc (m-L) (m+L)) J,
    overlap x u ∈ Icc (q-b) (q+b)}

/-- A closed random-set graph for the original critical-point band union.
Compact projection over the literal sphere handles even infinite fibers. -/
def originalEnergyBandUnionGraph (d : ℕ) (μ : FiniteMixture)
    (m L q b : ℝ) : Set (Disorder (d+2) μ.maxDegree × Vector (d+2)) :=
  {z | z.2 ∈ originalEnergyBandUnion d μ m L q b z.1}

theorem originalEnergyBandUnion_graph_isClosed (d : ℕ) (μ : FiniteMixture)
    (m L q b : ℝ) :
    IsClosed (originalEnergyBandUnionGraph d μ m L q b) := by
  let S : Set (Vector (d+2)) := {u | ‖u‖^2 = ((d+2 : ℕ) : ℝ)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (sourceSphere_compact (d+2))
  let C₀ : Set (Disorder (d+2) μ.maxDegree × Vector (d+2)) :=
    {z | ‖z.2‖^2 = ((d+2 : ℕ) : ℝ)} ∩
    {z | surfaceGradient (field (mixtureCoefficients μ) z.1) z.2 = 0} ∩
    {z | field (mixtureCoefficients μ) z.1 z.2 ∈ Icc (m-L) (m+L)}
  have hC₀ : IsClosed C₀ := by
    apply IsClosed.inter
    · apply IsClosed.inter
      · exact isClosed_eq (continuous_snd.norm.pow 2) continuous_const
      · exact isClosed_eq
          (source_surfaceGradient_joint_contDiff (mixtureCoefficients μ)).continuous
          continuous_const
    · exact isClosed_Icc.preimage (field_jointContinuous (mixtureCoefficients μ))
  let B₀ : Set (Vector (d+2) × Vector (d+2)) :=
    {z | overlap z.1 z.2 ∈ Icc (q-b) (q+b)}
  have hB₀ : IsClosed B₀ := by
    apply isClosed_Icc.preimage
    unfold overlap
    exact (continuous_fst.inner continuous_snd).div_const _
  let C : Set (Disorder (d+2) μ.maxDegree × S) :=
    {z | (z.1,z.2.1) ∈ C₀}
  let B : Set (Vector (d+2) × S) :=
    {z | (z.1,z.2.1) ∈ B₀}
  have hC : IsClosed C :=
    hC₀.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hB : IsClosed B :=
    hB₀.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hProj := SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC hB
  convert hProj using 1
  ext z
  constructor
  · rintro ⟨u, hu, hb⟩
    let v : S := ⟨u, hu.1⟩
    refine ⟨v, ?_, ?_⟩
    · exact ⟨⟨hu.1,hu.2.1⟩,hu.2.2⟩
    · exact hb
  · rintro ⟨v, hv, hb⟩
    exact ⟨v.1, ⟨v.2,hv.1.2,hv.2⟩, hb⟩

theorem originalEnergyBandUnion_measurable (d : ℕ) (μ : FiniteMixture)
    (m L q b : ℝ) (J : Disorder (d+2) μ.maxDegree) :
    MeasurableSet (originalEnergyBandUnion d μ m L q b J) := by
  have h : IsClosed (originalEnergyBandUnion d μ m L q b J) :=
    (originalEnergyBandUnion_graph_isClosed d μ m L q b).preimage
      (show Continuous (fun x : Vector (d+2) => (J, x)) from
        continuous_const.prodMk continuous_id)
  exact h.measurableSet

theorem originalEnergyBandUnion_mono (d : ℕ) (μ : FiniteMixture)
    (m q L L' b b' : ℝ) (hL : L ≤ L') (hb : b ≤ b')
    (J : Disorder (d+2) μ.maxDegree) :
    originalEnergyBandUnion d μ m L q b J ⊆
      originalEnergyBandUnion d μ m L' q b' J := by
  rintro x ⟨u, hu, hoverlap⟩
  refine ⟨u, ⟨hu.1, hu.2.1, ?_⟩, ?_⟩
  · exact ⟨by linarith [hu.2.2.1], by linarith [hu.2.2.2]⟩
  · exact ⟨by linarith [hoverlap.1], by linarith [hoverlap.2]⟩

/-- Original Gibbs mass outside all fixed-window microscopic bands. -/
def originalBandComplementMass (d : ℕ) (μ : FiniteMixture)
    (β m L q b : ℝ) (J : Disorder (d+2) μ.maxDegree) : ℝ :=
  (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)).real
    (originalEnergyBandUnion d μ m L q b J)ᶜ

theorem originalBandComplementMass_measurable (d : ℕ) (μ : FiniteMixture)
    (β m L q b : ℝ) :
    Measurable (originalBandComplementMass d μ β m L q b) := by
  have hgraph := (originalEnergyBandUnion_graph_isClosed d μ m L q b).measurableSet.compl
  have hm := (Kernel.measurable_kernel_prodMk_left
    (κ := allDimensionGibbsKernel (mixtureCoefficients μ) β) hgraph).ennreal_toReal
  change Measurable (fun J : Disorder (d+2) μ.maxDegree =>
    ((gibbsLaw (d+2) β (field (mixtureCoefficients μ) J))
      (originalEnergyBandUnion d μ m L q b J)ᶜ).toReal)
  simpa only [originalEnergyBandUnionGraph, allDimensionGibbsKernel_apply,
    Set.preimage_compl, Set.preimage_ofPred_eq, Set.ofPred_mem_eq] using hm

theorem originalBandComplementMass_mem_unit (d : ℕ) (μ : FiniteMixture)
    (β m L q b : ℝ) (J : Disorder (d+2) μ.maxDegree) :
    originalBandComplementMass d μ β m L q b J ∈ Icc 0 1 := by
  let : IsProbabilityMeasure (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β
      (field_contDiff (mixtureCoefficients μ) J).continuous
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem originalBandComplementMass_integrable (d : ℕ) (μ : FiniteMixture)
    (β m L q b : ℝ) :
    Integrable (originalBandComplementMass d μ β m L q b)
      (disorderLaw (d+2) μ.maxDegree) := by
  apply Integrable.of_bound
    (originalBandComplementMass_measurable d μ β m L q b).aestronglyMeasurable 1
  exact .of_forall fun J => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (originalBandComplementMass_mem_unit d μ β m L q b J).1]
    exact (originalBandComplementMass_mem_unit d μ β m L q b J).2

theorem originalBandComplementMass_antitone (d : ℕ) (μ : FiniteMixture)
    (β m q L L' b b' : ℝ) (hL : L ≤ L') (hb : b ≤ b')
    (J : Disorder (d+2) μ.maxDegree) :
    originalBandComplementMass d μ β m L' q b' J ≤
      originalBandComplementMass d μ β m L q b J := by
  let : IsProbabilityMeasure (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β
      (field_contDiff (mixtureCoefficients μ) J).continuous
  exact measureReal_mono (Set.compl_subset_compl.mpr
    (originalEnergyBandUnion_mono d μ m q L L' b b' hL hb J))

/-- The literal disorder average used by the pure capture conclusion. -/
def expectedOriginalBandComplementMass (d : ℕ) (μ : FiniteMixture)
    (β m L q b : ℝ) : ℝ :=
  ∫ J, originalBandComplementMass d μ β m L q b J
    ∂disorderLaw (d+2) μ.maxDegree

theorem expectedOriginalBandComplementMass_nonneg (d : ℕ) (μ : FiniteMixture)
    (β m L q b : ℝ) :
    0 ≤ expectedOriginalBandComplementMass d μ β m L q b := by
  exact integral_nonneg fun J =>
    (originalBandComplementMass_mem_unit d μ β m L q b J).1

theorem expectedOriginalBandComplementMass_antitone (d : ℕ) (μ : FiniteMixture)
    (β m q L L' b b' : ℝ) (hL : L ≤ L') (hb : b ≤ b') :
    expectedOriginalBandComplementMass d μ β m L' q b' ≤
      expectedOriginalBandComplementMass d μ β m L q b := by
  exact integral_mono
    (originalBandComplementMass_integrable d μ β m L' q b')
    (originalBandComplementMass_integrable d μ β m L q b)
    (fun J => originalBandComplementMass_antitone d μ β m q L L' b b' hL hb J)

/-- The original-field cap partition sum on an energy set. -/
def originalEnergyMarkedCount (d : ℕ) (μ : FiniteMixture)
    (β : ℝ) (E I : Set ℝ) (J : Disorder (d+2) μ.maxDegree) : ℝ≥0∞ :=
  ∑' u : originalEnergyCriticalSet d μ E J,
    originalBorelBandMark d μ β I J u

/-- The physical score window in the marked count is precisely the
original unnormalized energy window, also in the singular pure case. -/
theorem originalEnergyMarkedCount_eq_actualScoreWindowCount
    (d : ℕ) (μ : FiniteMixture) (β : ℝ)
    (E I : Set ℝ) (J : Disorder (d+2) μ.maxDegree) :
    originalEnergyMarkedCount d μ β E I J =
      actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) 1)
        (physicalEnergyWindow (d+2) E univ)
        (originalBorelBandMark d μ β I) J := by
  have hc : centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
    funext p
    simp [centerCoefficients]
  have hs : {u : Vector (d+2) | ‖u‖^2 = ((d+2 : ℕ) : ℝ) ∧
      surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
      actualScore (mixtureCoefficients μ) J u ∈
        physicalEnergyWindow (d+2) E univ} = originalEnergyCriticalSet d μ E J := by
    ext u
    simp only [Set.mem_ofPred_eq]
    rw [actualScore_mem_physicalEnergyWindow (by omega : d+2 ≠ 0)]
    simp only [Set.mem_univ, and_true, originalEnergyCriticalSet, Set.mem_ofPred_eq]
  unfold originalEnergyMarkedCount actualScoreWindowCount
  rw [hc]
  change (∑' u : originalEnergyCriticalSet d μ E J,
      originalBorelBandMark d μ β I J u) =
    ∑' u : {u : Vector (d+2) | ‖u‖^2 = ((d+2 : ℕ) : ℝ) ∧
      surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
      actualScore (mixtureCoefficients μ) J u ∈ physicalEnergyWindow (d+2) E univ},
      originalBorelBandMark d μ β I J u
  rw [hs]

/-- A point of the coarse cap cover missed by the microscopic fixed-window
bands lies either in a below-window cap or in a fixed-window angular error.
The upper maximum event is the only additional deterministic condition. -/
theorem original_band_complement_subset (d : ℕ) (μ : FiniteMixture)
    (a ep τ m L q b : ℝ) (J : Disorder (d+2) μ.maxDegree)
    (hmax : ∀ u : Vector (d+2), ‖u‖^2 = ((d+2 : ℕ) : ℝ) →
      field (mixtureCoefficients μ) J u ≤ m+L) :
    (originalEnergyBandUnion d μ m L q b J)ᶜ ⊆
      (coarseCriticalCapCover d μ a ep τ J)ᶜ ∪
        ((⋃ u ∈ originalEnergyCriticalSet d μ
            (Icc ((d+2 : ℕ)*(ep-τ)) (m-L)) J,
            overlapRegion u (Ici a)) ∪
          (⋃ u ∈ originalEnergyCriticalSet d μ (Icc (m-L) (m+L)) J,
            overlapRegion u (Ici a \ Icc (q-b) (q+b)))) := by
  intro x hx
  by_cases hcoarse : x ∈ coarseCriticalCapCover d μ a ep τ J
  · rcases hcoarse with ⟨u, hu, hcrit, henergy, hcap⟩
    apply Or.inr
    by_cases hdeep : field (mixtureCoefficients μ) J u ≤ m-L
    · apply Or.inl
      exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr
        ⟨⟨hu, hcrit, henergy, hdeep⟩, hcap⟩⟩
    · apply Or.inr
      have hw : u ∈ originalEnergyCriticalSet d μ (Icc (m-L) (m+L)) J :=
        ⟨hu, hcrit, (lt_of_not_ge hdeep).le, hmax u hu⟩
      have hnot : overlap x u ∉ Icc (q-b) (q+b) := by
        intro hi
        exact hx ⟨u, hw, hi⟩
      exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hw, hcap, hnot⟩⟩
  · exact Or.inl hcoarse

theorem originalEnergyCriticalSet_finite (d : ℕ) (μ : FiniteMixture)
    (J : Disorder (d+2) μ.maxDegree)
    (hf : (originalEnergyCriticalSet d μ univ J).Finite) (E : Set ℝ) :
    (originalEnergyCriticalSet d μ E J).Finite :=
  hf.subset fun _ h => ⟨h.1, h.2.1, Set.mem_univ _⟩

theorem originalEnergyCriticalSet_finite_ae (d : ℕ) (μ : FiniteMixture) :
    ∀ᵐ J ∂disorderLaw (d+2) μ.maxDegree,
      (originalEnergyCriticalSet d μ univ J).Finite := by
  have h := actual_sphere_criticalSet_finite_ae (d+1) (by omega) μ
    (Q := 1) (by norm_num)
  simpa only [originalEnergyCriticalSet, sphereCriticalSet, Set.mem_univ,
    and_true, show d+1+1 = d+2 by omega,
    show centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ by
      funext p
      simp [centerCoefficients]] using h

theorem originalEnergyMarkedCount_toReal (d : ℕ) (μ : FiniteMixture)
    (β : ℝ) (E I : Set ℝ) (J : Disorder (d+2) μ.maxDegree)
    [Fintype (originalEnergyCriticalSet d μ E J)] :
    (originalEnergyMarkedCount d μ β E I J).toReal =
      ∑ u : originalEnergyCriticalSet d μ E J,
        partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I) := by
  classical
  unfold originalEnergyMarkedCount originalBorelBandMark
  rw [tsum_fintype, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro u _
  exact ENNReal.toReal_ofReal (partitionOn_nonneg β _ _)

/-- Finite critical-point sums use the same original Gibbs normalizer as
their partition marks. No Palm law or thermodynamic estimate is involved. -/
theorem originalEnergy_gibbs_sum_eq_marked_count (d : ℕ) (μ : FiniteMixture)
    (β : ℝ) (E : Set ℝ) {I : Set ℝ} (hI : MeasurableSet I)
    (J : Disorder (d+2) μ.maxDegree)
    [Fintype (originalEnergyCriticalSet d μ E J)] :
    (∑ u : originalEnergyCriticalSet d μ E J,
      (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)).real
        (overlapRegion u I)) =
      (originalEnergyMarkedCount d μ β E I J).toReal /
        partition (d+2) β (field (mixtureCoefficients μ) J) := by
  classical
  rw [originalEnergyMarkedCount_toReal, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  exact gibbsLaw_real_eq_partitionOn_div (by omega) β
    (field_contDiff (mixtureCoefficients μ) J).continuous
    (overlapRegion_measurable (u : Vector (d+2)) hI)

/-- Finite fibers suffice for the actual cap-to-band comparison. The
exceptional infinite fibers are removed by the already proved Gaussian
critical-set finiteness theorem in the probabilistic application. -/
theorem original_gibbs_band_complement_le (d : ℕ) (hd : 1 ≤ d)
    (μ : FiniteMixture) (β a ep τ m L q b : ℝ)
    (J : Disorder (d+2) μ.maxDegree)
    (hf : (originalEnergyCriticalSet d μ univ J).Finite)
    (hmax : ∀ u : Vector (d+2), ‖u‖^2 = ((d+2 : ℕ) : ℝ) →
      field (mixtureCoefficients μ) J u ≤ m+L) :
    (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)).real
        (originalEnergyBandUnion d μ m L q b J)ᶜ ≤
      uncoveredGibbsMass d μ β a ep τ J +
        ((originalEnergyMarkedCount d μ β
            (Icc ((d+2 : ℕ)*(ep-τ)) (m-L)) (Ico a 1) J).toReal +
          (originalEnergyMarkedCount d μ β (Icc (m-L) (m+L))
            (Ico a 1 \ Icc (q-b) (q+b)) J).toReal) /
          partition (d+2) β (field (mixtureCoefficients μ) J) := by
  classical
  let H := field (mixtureCoefficients μ) J
  let π := gibbsLaw (d+2) β H
  let D := originalEnergyCriticalSet d μ (Icc ((d+2 : ℕ)*(ep-τ)) (m-L)) J
  let W := originalEnergyCriticalSet d μ (Icc (m-L) (m+L)) J
  let : Fintype D := (originalEnergyCriticalSet_finite d μ J hf _).fintype
  let : Fintype W := (originalEnergyCriticalSet_finite d μ J hf _).fintype
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  let DC := ⋃ u : D, overlapRegion (u : Vector (d+2)) (Ici a)
  let AC := ⋃ u : W, overlapRegion (u : Vector (d+2)) (Ici a \ Icc (q-b) (q+b))
  have hsub : (originalEnergyBandUnion d μ m L q b J)ᶜ ⊆
      (coarseCriticalCapCover d μ a ep τ J)ᶜ ∪ (DC ∪ AC) := by
    intro x hx
    rcases original_band_complement_subset d μ a ep τ m L q b J hmax hx with h | h
    · exact Or.inl h
    · apply Or.inr
      rcases h with h | h
      · rcases Set.mem_iUnion.mp h with ⟨u, hu⟩
        rcases Set.mem_iUnion.mp hu with ⟨hcrit, hcap⟩
        exact Or.inl (Set.mem_iUnion.mpr ⟨⟨u, hcrit⟩, hcap⟩)
      · rcases Set.mem_iUnion.mp h with ⟨u, hu⟩
        rcases Set.mem_iUnion.mp hu with ⟨hcrit, hcap⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨u, hcrit⟩, hcap⟩)
  have hD : π.real DC ≤ ∑ u : D, π.real (overlapRegion (u : Vector (d+2)) (Ici a)) :=
    measureReal_iUnion_fintype_le _
  have hA : π.real AC ≤
      ∑ u : W, π.real (overlapRegion (u : Vector (d+2)) (Ici a \ Icc (q-b) (q+b))) :=
    measureReal_iUnion_fintype_le _
  have hDsum : (∑ u : D, π.real (overlapRegion (u : Vector (d+2)) (Ici a))) =
      (originalEnergyMarkedCount d μ β
        (Icc ((d+2 : ℕ)*(ep-τ)) (m-L)) (Ico a 1) J).toReal /
        partition (d+2) β H := by
    calc
      _ = ∑ u : D, π.real (overlapRegion (u : Vector (d+2)) (Ico a 1)) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [gibbsLaw_real_eq_partitionOn_div (by omega) β
            (field_contDiff (mixtureCoefficients μ) J).continuous
            (overlapRegion_measurable (u : Vector (d+2)) measurableSet_Ici),
          gibbsLaw_real_eq_partitionOn_div (by omega) β
            (field_contDiff (mixtureCoefficients μ) J).continuous
            (overlapRegion_measurable (u : Vector (d+2)) measurableSet_Ico)]
        rw [partitionOn_closed_cap_eq_half_open (by omega : 2 ≤ d+1) β
          (field_contDiff (mixtureCoefficients μ) J).continuous u u.2.1 a]
      _ = _ := originalEnergy_gibbs_sum_eq_marked_count d μ β _ measurableSet_Ico J
  have hAsum : (∑ u : W, π.real (overlapRegion (u : Vector (d+2)) (Ici a \ Icc (q-b) (q+b)))) =
      (originalEnergyMarkedCount d μ β (Icc (m-L) (m+L))
        (Ico a 1 \ Icc (q-b) (q+b)) J).toReal /
        partition (d+2) β H := by
    calc
      _ = ∑ u : W, π.real (overlapRegion (u : Vector (d+2)) (Ico a 1 \ Icc (q-b) (q+b))) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [gibbsLaw_real_eq_partitionOn_div (by omega) β
            (field_contDiff (mixtureCoefficients μ) J).continuous
            (overlapRegion_measurable (u : Vector (d+2)) (measurableSet_Ici.diff measurableSet_Icc)),
          gibbsLaw_real_eq_partitionOn_div (by omega) β
            (field_contDiff (mixtureCoefficients μ) J).continuous
            (overlapRegion_measurable (u : Vector (d+2)) (measurableSet_Ico.diff measurableSet_Icc))]
        rw [partitionOn_closed_cap_difference_eq_half_open (by omega : 2 ≤ d+1) β
          (field_contDiff (mixtureCoefficients μ) J).continuous u u.2.1 a measurableSet_Icc]
      _ = _ := originalEnergy_gibbs_sum_eq_marked_count d μ β _
        (measurableSet_Ico.diff measurableSet_Icc) J
  have hmono := measureReal_mono (μ := π) hsub
  have hU := measureReal_union_le (μ := π)
    (coarseCriticalCapCover d μ a ep τ J)ᶜ (DC ∪ AC)
  have hV := measureReal_union_le (μ := π) DC AC
  rw [hDsum] at hD
  rw [hAsum] at hA
  dsimp only [uncoveredGibbsMass]
  rw [add_div]
  change π.real _ ≤ π.real _ + (_ + _)
  linarith

end SlowEquilibration.SourcePureCaptureBandComplementBound
