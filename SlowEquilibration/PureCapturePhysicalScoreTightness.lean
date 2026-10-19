-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureConditionalCoarseWeakLimit
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Uniform tightness of each finite-dimensional physical overlap-score
law, using only the exact spherical support of the original Gibbs law.
This is a finite-coordinate prerequisite for a simultaneous infinite
overlap-array subsequence and Dovbysh–Sudakov representation. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalScoreTightness

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open SphericalAging.HardSphereDynamics
open PureCaptureOverlapScoreCoordinates
open PureCaptureScorePortmanteauTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalFiniteMeasurability
open PureCaptureConditionalCoarseWeakLimit
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- A fixed compact cube containing all coordinates of overlap scores
of physical sphere replicas, uniformly in the physical dimension. -/
def scoreCube (k T : ℕ) : Set (ScoreCoordinates k T) :=
  (Set.pi univ (fun _ : Fin T =>
    Set.pi univ (fun _ : Fin k => Icc (-1 : ℝ) 1))) ×ˢ
  (Set.pi univ (fun _ : Fin T =>
    Set.pi univ (fun _ : Fin k =>
      Set.pi univ (fun _ : Fin k => Icc (-1 : ℝ) 1))))

theorem scoreCube_compact (k T : ℕ) : IsCompact (scoreCube k T) := by
  unfold scoreCube
  exact (isCompact_univ_pi (fun _ : Fin T =>
    isCompact_univ_pi (fun _ : Fin k => isCompact_Icc))).prod
      (isCompact_univ_pi (fun _ : Fin T =>
        isCompact_univ_pi (fun _ : Fin k =>
          isCompact_univ_pi (fun _ : Fin k => isCompact_Icc))))

/-- All overlap-score coordinates of any on-sphere finite physical
ensemble lie in the same cube. -/
theorem physicalScoreCoordinates_mem_scoreCube {n k T : ℕ}
    {p : PhysicalEnsemble (n+2) k T}
    (hp : p ∈ allPhysicalSpinsOnSphere) :
    physicalScoreCoordinates p ∈ scoreCube k T := by
  obtain ⟨hx, hσ⟩ := hp
  change (∀ b : Fin T, b ∈ univ →
      ∀ i : Fin k, i ∈ univ → overlap p.1 (p.2 b i) ∈ Icc (-1 : ℝ) 1) ∧
    (∀ b : Fin T, b ∈ univ → ∀ i : Fin k, i ∈ univ →
      ∀ j : Fin k, j ∈ univ →
      (if i = j then 0 else overlap (p.2 b i) (p.2 b j)) ∈ Icc (-1 : ℝ) 1)
  constructor
  · intro b _ i _
    exact overlap_mem_Icc_of_norm_sq (by omega : 1 ≤ n+2) p.1 (p.2 b i)
      ((onSphere_iff_norm_sq p.1).mp hx)
      ((onSphere_iff_norm_sq (p.2 b i)).mp (hσ b i))
  · intro b _ i _ j _
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using
        (overlap_mem_Icc_of_norm_sq (by omega : 1 ≤ n+2) (p.2 b i) (p.2 b j)
          ((onSphere_iff_norm_sq (p.2 b i)).mp (hσ b i))
          ((onSphere_iff_norm_sq (p.2 b j)).mp (hσ b j)))

theorem annealedPhysicalEnsembleLaw_sphere_ae {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ p ∂annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β,
      p ∈ allPhysicalSpinsOnSphere := by
  apply mem_ae_iff.mpr
  unfold annealedPhysicalEnsembleLaw
  change ((disorderLaw (n+2) μ.maxDegree).bind
    (physicalEnsembleKernel (n := n) (k := k) (T := T) μ β))
      (allPhysicalSpinsOnSphere (N := n+2) (k := k) (T := T))ᶜ = 0
  rw [Measure.bind_apply allPhysicalSpinsOnSphere_measurable.compl
    (physicalEnsembleKernel μ β).aemeasurable]
  have hzero (J : Disorder (n+2) μ.maxDegree) :
      (physicalEnsembleKernel (n := n) (k := k) (T := T) μ β J)
        (allPhysicalSpinsOnSphere (N := n+2) (k := k) (T := T))ᶜ = 0 := by
    rw [physicalEnsembleKernel_apply]
    exact mem_ae_iff.mp (physicalEnsembleLaw_sphere_ae (k := k) (T := T) μ β J)
  have hfun : (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleKernel (n := n) (k := k) (T := T) μ β J)
        (allPhysicalSpinsOnSphere (N := n+2) (k := k) (T := T))ᶜ) =
      (fun _ => 0) := funext hzero
  rw [hfun]
  simp

theorem annealedPhysicalScoreLaw_cube_ae {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ c ∂(annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β :
      Measure (ScoreCoordinates k T)), c ∈ scoreCube k T := by
  have hcube : MeasurableSet (scoreCube k T) := (scoreCube_compact k T).isClosed.measurableSet
  unfold annealedPhysicalScoreLaw
  apply (ae_map_iff physicalScoreCoordinates_continuous.measurable.aemeasurable hcube).2
  exact (annealedPhysicalEnsembleLaw_sphere_ae μ β).mono
    (fun p hp => physicalScoreCoordinates_mem_scoreCube hp)

/-- For fixed k and T, the original annealed overlap-score laws have
compact weak closure as the physical dimension varies. -/
theorem annealedPhysicalScoreLaws_compact_closure {k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (closure (Set.range (fun n : ℕ =>
      annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β))) := by
  apply isCompact_closure_of_isTightMeasureSet
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε _
  refine ⟨scoreCube k T, scoreCube_compact k T, ?_⟩
  intro ρ hρ
  obtain ⟨ν, ⟨n, rfl⟩, rfl⟩ := hρ
  have hzero : (annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β :
      Measure (ScoreCoordinates k T)) (scoreCube k T)ᶜ = 0 :=
    mem_ae_iff.mp (annealedPhysicalScoreLaw_cube_ae μ β)
  rw [hzero]
  exact bot_le

/-- Every sequence of physical dimensions has a further subsequence
whose fixed finite overlap-score law converges weakly. -/
theorem annealedPhysicalScoreLaws_tendsto_subseq {k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) (s : ℕ → ℕ) :
    ∃ limitLaw ∈ closure (Set.range (fun n : ℕ =>
        annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β)),
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun m : ℕ =>
          annealedPhysicalScoreLaw (n := s (t m)) (k := k) (T := T) μ β)
          atTop (𝓝 limitLaw) := by
  apply (annealedPhysicalScoreLaws_compact_closure (k := k) (T := T) μ β).tendsto_subseq
    (x := fun m => annealedPhysicalScoreLaw (n := s m) (k := k) (T := T) μ β)
  intro m
  exact subset_closure (Set.mem_range.mpr ⟨s m, rfl⟩)

/-- The physical overlap array viewed through all of its finite block
score laws at once. -/
abbrev ScoreLawArray (k : ℕ) :=
  (T : ℕ) → ProbabilityMeasure (ScoreCoordinates k T)

def annealedPhysicalScoreLawArray (k : ℕ) (μ : FiniteMixture)
    (β : ℝ) (n : ℕ) : ScoreLawArray k :=
  fun T => annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β

def physicalScoreLawArrayLimitSet (k : ℕ) (μ : FiniteMixture)
    (β : ℝ) : Set (ScoreLawArray k) :=
  closure (Set.range (annealedPhysicalScoreLawArray k μ β))

/-- All possible simultaneous finite-coordinate weak-limit families of
the original physical score laws form a compact set. -/
theorem physicalScoreLawArrayLimitSet_compact (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (physicalScoreLawArrayLimitSet k μ β) := by
  let C (T : ℕ) : Set (ProbabilityMeasure (ScoreCoordinates k T)) :=
    closure (Set.range (fun n : ℕ =>
      annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β))
  have hC (T : ℕ) : IsCompact (C T) :=
    annealedPhysicalScoreLaws_compact_closure μ β
  have hprod : IsCompact (Set.pi univ C) := isCompact_univ_pi hC
  have hrange : Set.range (annealedPhysicalScoreLawArray k μ β) ⊆
      Set.pi univ C := by
    intro x hx T _
    obtain ⟨n, rfl⟩ := hx
    exact subset_closure (Set.mem_range.mpr ⟨n, rfl⟩)
  exact hprod.closure_of_subset hrange

/-- Every sequence of physical dimensions admits a single subsequence
on which the annealed overlap-score laws converge simultaneously for
all finite block counts. This stops short of identifying the limit as a
Dovbysh–Sudakov directing ensemble. -/
theorem physicalScoreLawArrayLimitSet_tendsto_subseq (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) (s : ℕ → ℕ) :
    ∃ limitArray ∈ physicalScoreLawArrayLimitSet k μ β,
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun m : ℕ => annealedPhysicalScoreLawArray k μ β (s (t m)))
          atTop (𝓝 limitArray) := by
  apply (physicalScoreLawArrayLimitSet_compact k μ β).tendsto_subseq
    (x := fun m => annealedPhysicalScoreLawArray k μ β (s m))
  intro m
  exact subset_closure (Set.mem_range.mpr ⟨s m, rfl⟩)

/-- Physical source-9.16 finite failure vanishes after choosing enough
companion blocks, conditional only on block consistency and pointwise
companion extraction for the *actual* simultaneous weak-limit family.
Compactness and the required physical weak subsequences are proved above. -/
theorem expectedFiniteFailure_eventually_small_of_physical_array_limits
    {k : ℕ} (μ : FiniteMixture) (β Q θ : ℝ)
    (hanti : ∀ x ∈ physicalScoreLawArrayLimitSet k μ β,
      ∀ (s t : ℕ), s ≤ t →
        ((x t : Measure (ScoreCoordinates k t)) (scoreFailure Q θ)).toReal ≤
        ((x s : Measure (ScoreCoordinates k s)) (scoreFailure Q θ)).toReal)
    (hpoint : ∀ x ∈ physicalScoreLawArrayLimitSet k μ β,
      Tendsto (fun T =>
        ((x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal)
        atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  let K := physicalScoreLawArrayLimitSet k μ β
  let : CompactSpace K :=
    isCompact_iff_compactSpace.mp (physicalScoreLawArrayLimitSet_compact k μ β)
  apply expectedFiniteFailure_eventually_small_of_compact_cluster_limits
    μ β Q θ (univ : Set K) isCompact_univ
    (fun T x => x.1 T)
    (fun T => (continuous_apply T).comp continuous_subtype_val)
    ?_ ?_ ?_ ε hε
  · intro s t hst x
    exact hanti x.1 x.2 s t hst
  · intro x _
    exact hpoint x.1 x.2
  · intro T s _
    obtain ⟨L, hL, t, ht, hlim⟩ :=
      physicalScoreLawArrayLimitSet_tendsto_subseq k μ β s
    refine ⟨⟨L, hL⟩, t, mem_univ _, ht, ?_⟩
    change Tendsto (fun m =>
      (annealedPhysicalScoreLawArray k μ β (s (t m))) T) atTop (𝓝 (L T))
    exact ((continuous_apply T).tendsto L).comp hlim

end SlowEquilibration.PureCapturePhysicalScoreTightness
