-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullOverlapArray

/-! A genuine probability law on the countably infinite overlap-array
space, obtained as a weak subsequential limit of zero-padded ordinary
finite Gibbs overlap arrays. The next module identifies every finite
prefix with the corresponding full finite-array limit. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalInfiniteArrayTightness

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

abbrev InfiniteOverlapCoordinates := ℕ → ℕ → ℝ

def infiniteOverlapCube : Set InfiniteOverlapCoordinates :=
  Set.pi univ (fun _ : ℕ => Set.pi univ (fun _ : ℕ => Icc (-1 : ℝ) 1))

theorem infiniteOverlapCube_compact : IsCompact infiniteOverlapCube := by
  unfold infiniteOverlapCube
  exact isCompact_univ_pi (fun _ : ℕ =>
    isCompact_univ_pi (fun _ : ℕ => isCompact_Icc))

def padFullOverlap (m : ℕ) (c : FullOverlapCoordinates m) :
    InfiniteOverlapCoordinates :=
  fun i j => if hi : i < m then
    if hj : j < m then c ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else 0

theorem padFullOverlap_continuous (m : ℕ) : Continuous (padFullOverlap m) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hi : i < m
  · by_cases hj : j < m
    · simpa only [padFullOverlap, hi, hj, dite_eq_left, Function.comp_def] using
        ((continuous_apply (⟨j, hj⟩ : Fin m)).comp
          (continuous_apply (⟨i, hi⟩ : Fin m)))
    · simpa [padFullOverlap, hi, hj] using
        (continuous_const : Continuous (fun _ : FullOverlapCoordinates m => (0 : ℝ)))
  · simpa [padFullOverlap, hi] using
      (continuous_const : Continuous (fun _ : FullOverlapCoordinates m => (0 : ℝ)))

theorem padFullOverlap_mem_cube {m : ℕ} {c : FullOverlapCoordinates m}
    (hc : c ∈ fullOverlapCube m) :
    padFullOverlap m c ∈ infiniteOverlapCube := by
  change ∀ i : ℕ, i ∈ univ → ∀ j : ℕ, j ∈ univ →
    padFullOverlap m c i j ∈ Icc (-1 : ℝ) 1
  intro i _ j _
  by_cases hi : i < m
  · by_cases hj : j < m
    · simpa [padFullOverlap, hi, hj] using
        (hc (⟨i, hi⟩ : Fin m) (mem_univ _) (⟨j, hj⟩ : Fin m) (mem_univ _))
    · simp [padFullOverlap, hi, hj]
  · simp [padFullOverlap, hi]

def physicalPaddedFullOverlapLaw (n : ℕ) (μ : FiniteMixture) (β : ℝ) :
    ProbabilityMeasure InfiniteOverlapCoordinates :=
  (physicalFullOverlapLaw (n := n) (m := n+1) μ β).map (padFullOverlap (n+1))

theorem physicalPaddedFullOverlapLaw_cube_ae (n : ℕ)
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ c ∂(physicalPaddedFullOverlapLaw n μ β : Measure InfiniteOverlapCoordinates),
      c ∈ infiniteOverlapCube := by
  have hcube : MeasurableSet infiniteOverlapCube :=
    infiniteOverlapCube_compact.isClosed.measurableSet
  unfold physicalPaddedFullOverlapLaw
  apply (ae_map_iff (padFullOverlap_continuous _).measurable.aemeasurable hcube).2
  exact (physicalFullOverlapLaw_cube_ae μ β).mono
    (fun c hc => padFullOverlap_mem_cube hc)

theorem physicalPaddedFullOverlapLaws_compact_closure
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (closure (Set.range (fun n : ℕ =>
      physicalPaddedFullOverlapLaw n μ β))) := by
  apply isCompact_closure_of_isTightMeasureSet
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε _
  refine ⟨infiniteOverlapCube, infiniteOverlapCube_compact, ?_⟩
  intro ρ hρ
  obtain ⟨ν, ⟨n, rfl⟩, rfl⟩ := hρ
  have hzero : (physicalPaddedFullOverlapLaw n μ β :
      Measure InfiniteOverlapCoordinates) infiniteOverlapCubeᶜ = 0 :=
    mem_ae_iff.mp (physicalPaddedFullOverlapLaw_cube_ae n μ β)
  rw [hzero]
  exact bot_le

theorem physicalPaddedFullOverlapLaws_tendsto_subseq
    (μ : FiniteMixture) (β : ℝ) (s : ℕ → ℕ) :
    ∃ limitLaw ∈ closure (Set.range (fun n : ℕ =>
        physicalPaddedFullOverlapLaw n μ β)),
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun j : ℕ => physicalPaddedFullOverlapLaw (s (t j)) μ β)
          atTop (𝓝 limitLaw) := by
  apply (physicalPaddedFullOverlapLaws_compact_closure μ β).tendsto_subseq
    (x := fun j => physicalPaddedFullOverlapLaw (s j) μ β)
  intro j
  exact subset_closure (Set.mem_range.mpr ⟨s j, rfl⟩)

def fullOverlapTruncate {m p : ℕ} (h : m ≤ p)
    (c : FullOverlapCoordinates p) : FullOverlapCoordinates m :=
  fun i j => c (i.castLE h) (j.castLE h)

theorem fullOverlapTruncate_continuous {m p : ℕ} (h : m ≤ p) :
    Continuous (fullOverlapTruncate h) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (j.castLE h)).comp
    (continuous_apply (i.castLE h))

theorem fullOverlapTruncate_refl {m : ℕ} (c : FullOverlapCoordinates m) :
    fullOverlapTruncate (Nat.le_refl m) c = c := by
  ext i j
  rfl

theorem fullOverlapTruncate_succ {m p : ℕ} (h : m ≤ p)
    (c : FullOverlapCoordinates (p+1)) :
    fullOverlapTruncate (Nat.le_trans h (Nat.le_succ p)) c =
      fullOverlapTruncate h (fullOverlapPrefix c) := by
  ext i j
  rfl

def infiniteTruncate (m : ℕ) (c : InfiniteOverlapCoordinates) :
    FullOverlapCoordinates m :=
  fun i j => c i.val j.val

theorem infiniteTruncate_continuous (m : ℕ) :
    Continuous (infiniteTruncate m) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply j.val).comp (continuous_apply i.val)

theorem infiniteTruncate_padFullOverlap {m p : ℕ} (h : m ≤ p)
    (c : FullOverlapCoordinates p) :
    infiniteTruncate m (padFullOverlap p c) = fullOverlapTruncate h c := by
  ext i j
  simp [infiniteTruncate, padFullOverlap, fullOverlapTruncate,
    lt_of_lt_of_le i.isLt h, lt_of_lt_of_le j.isLt h]
  congr 1

theorem physicalFullOverlapLaw_map_truncate {n m p : ℕ}
    (μ : FiniteMixture) (β : ℝ) (h : m ≤ p) :
    (physicalFullOverlapLaw (n := n) (m := p) μ β).map
      (fullOverlapTruncate h) =
    physicalFullOverlapLaw (n := n) (m := m) μ β := by
  induction p generalizing m with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst m
    apply ProbabilityMeasure.toMeasure_injective
    change ((physicalFullOverlapLaw (n := n) (m := 0) μ β :
      Measure (FullOverlapCoordinates 0)).map (fullOverlapTruncate h)) = _
    have hfun : fullOverlapTruncate h = id := by
      funext c
      exact fullOverlapTruncate_refl c
    rw [hfun, Measure.map_id]
  | succ p ih =>
    by_cases hm : m ≤ p
    · apply ProbabilityMeasure.toMeasure_injective
      change ((physicalFullOverlapLaw (n := n) (m := p+1) μ β :
        Measure (FullOverlapCoordinates (p+1))).map
          (fullOverlapTruncate h)) =
        (physicalFullOverlapLaw (n := n) (m := m) μ β :
          Measure (FullOverlapCoordinates m))
      have hfun : fullOverlapTruncate h =
          (fullOverlapTruncate hm) ∘ fullOverlapPrefix := by
        funext c
        exact fullOverlapTruncate_succ hm c
      rw [hfun, ← Measure.map_map (fullOverlapTruncate_continuous hm).measurable
        fullOverlapPrefix_continuous.measurable]
      have hp := physicalFullOverlapLaw_map_prefix (n := n) (m := p) μ β
      have hi := ih hm
      have hpM : ((physicalFullOverlapLaw (n := n) (m := p+1) μ β :
          Measure (FullOverlapCoordinates (p+1))).map fullOverlapPrefix) =
          (physicalFullOverlapLaw (n := n) (m := p) μ β :
            Measure (FullOverlapCoordinates p)) :=
        congrArg (fun ρ : ProbabilityMeasure (FullOverlapCoordinates p) =>
          (ρ : Measure (FullOverlapCoordinates p))) hp
      rw [hpM]
      exact congrArg (fun ρ : ProbabilityMeasure (FullOverlapCoordinates m) =>
        (ρ : Measure (FullOverlapCoordinates m))) hi
    · have heq : m = p+1 := by omega
      subst m
      apply ProbabilityMeasure.toMeasure_injective
      change ((physicalFullOverlapLaw (n := n) (m := p+1) μ β :
        Measure (FullOverlapCoordinates (p+1))).map
          (fullOverlapTruncate h)) = _
      have hfun : fullOverlapTruncate h = id := by
        funext c
        exact fullOverlapTruncate_refl c
      rw [hfun, Measure.map_id]

theorem physicalPaddedFullOverlapLaw_map_truncate
    {n m : ℕ} (μ : FiniteMixture) (β : ℝ) (h : m ≤ n+1) :
    (physicalPaddedFullOverlapLaw n μ β).map (infiniteTruncate m) =
      physicalFullOverlapLaw (n := n) (m := m) μ β := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((physicalFullOverlapLaw (n := n) (m := n+1) μ β :
    Measure (FullOverlapCoordinates (n+1))).map (padFullOverlap (n+1))).map
      (infiniteTruncate m) =
    (physicalFullOverlapLaw (n := n) (m := m) μ β :
      Measure (FullOverlapCoordinates m))
  rw [Measure.map_map (infiniteTruncate_continuous m).measurable
    (padFullOverlap_continuous (n+1)).measurable]
  have hcomp : (infiniteTruncate m) ∘ padFullOverlap (n+1) =
      fullOverlapTruncate h := by
    funext c
    exact infiniteTruncate_padFullOverlap h c
  rw [hcomp]
  exact congrArg (fun ρ : ProbabilityMeasure (FullOverlapCoordinates m) =>
    (ρ : Measure (FullOverlapCoordinates m)))
    (physicalFullOverlapLaw_map_truncate μ β h)

def infiniteToFullLawArray
    (ρ : ProbabilityMeasure InfiniteOverlapCoordinates) : FullOverlapLawArray :=
  fun m => ρ.map (infiniteTruncate m)

theorem infiniteToFullLawArray_continuous :
    Continuous infiniteToFullLawArray := by
  apply continuous_pi
  intro m
  exact ProbabilityMeasure.continuous_map (infiniteTruncate_continuous m)

theorem fullOverlapLawArray_tendsto_of_padded_tendsto
    (μ : FiniteMixture) (β : ℝ) (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hlim : Tendsto (fun j => physicalPaddedFullOverlapLaw (s j) μ β)
      atTop (𝓝 ρ)) :
    Tendsto (fun j => physicalFullOverlapLawArray μ β (s j))
      atTop (𝓝 (infiniteToFullLawArray ρ)) := by
  apply tendsto_pi_nhds.mpr
  intro m
  have hev : ∀ᶠ j : ℕ in atTop, m ≤ s j + 1 :=
    (hs.eventually (eventually_ge_atTop m)).mono (fun j hj => by omega)
  have hmap := ((ProbabilityMeasure.continuous_map
    (infiniteTruncate_continuous m)).tendsto ρ).comp hlim
  apply hmap.congr'
  filter_upwards [hev] with j hj
  exact physicalPaddedFullOverlapLaw_map_truncate μ β hj

theorem infiniteArrayLimit_projects_to_fullArrayLimit
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hseq : ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧
      Tendsto (fun j => physicalPaddedFullOverlapLaw (s j) μ β)
        atTop (𝓝 ρ)) :
    infiniteToFullLawArray ρ ∈ physicalFullOverlapArrayLimitSet μ β := by
  obtain ⟨s, hs, hlim⟩ := hseq
  have hfull := fullOverlapLawArray_tendsto_of_padded_tendsto μ β s hs hlim
  exact isClosed_closure.mem_of_tendsto hfull
    (Filter.Eventually.of_forall (fun j =>
      subset_closure (Set.mem_range.mpr ⟨s j, rfl⟩)))

end SlowEquilibration.PureCapturePhysicalInfiniteArrayTightness
