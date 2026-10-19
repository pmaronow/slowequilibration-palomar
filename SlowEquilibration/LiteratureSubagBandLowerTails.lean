-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerProof
public import SlowEquilibration.SourcePureCaptureReplicaNetGeometry
public import SlowEquilibration.SphericalGibbsMass

/-!
Finite dimensional steps in the uniform slab argument of Subag's Lemma 20.
Every spherical tuple has an orthogonal frame with unit coordinate vectors;
Cauchy's inequality records the square root of the frame size in the slab
width. Products of sphere nets give the exact exponential covering entropy.
The outer probability decomposition exposes the full partition denominator
once, before taking the net union of unnormalized slab lower tail events.
Some positive exponential slab rate then gives a positive replicated block
rate, including absorption of the finite number of replicas.

The fixed tuple unnormalized slab tails and Lemma 22's superconcentration
estimate are not asserted here. The separate arbitrary rate Gibbs corollaries
are formal implications retaining their stronger lower tail premises; those
premises are not asserted to follow from the unnormalized pressure estimate.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerTails

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem10Final LiteratureSubagBandLowerProof
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The lower tail at a single deterministic tuple of slab directions. -/
def fixedSlabLowerTailEvent {N j : ℕ} (μ : FiniteMixture) (β ρ t : ℝ)
    (σ : Fin j → Vector N) : Set (Disorder N μ.maxDegree) :=
  {J | (gibbsLaw N β (fieldOfMixture μ J)).real
      {y | ∀ i, |overlap y (σ i)| < ρ} < Real.exp (-t * (N : ℝ))}

/-- The actual unnormalized partition integral in a deterministic slab. -/
def fixedSlabPartition {N j : ℕ} (μ : FiniteMixture) (β ρ : ℝ)
    (J : Disorder N μ.maxDegree) (σ : Fin j → Vector N) : ℝ :=
  partitionOn β (fieldOfMixture μ J) {y | ∀ i, |overlap y (σ i)| < ρ}

/-- An unnormalized slab lower tail centered at the full mean pressure. -/
def fixedSlabPartitionLowerTailEvent {N j : ℕ} (μ : FiniteMixture) (β ρ t : ℝ)
    (σ : Fin j → Vector N) : Set (Disorder N μ.maxDegree) :=
  {J | fixedSlabPartition μ β ρ J σ <
    Real.exp ((N : ℝ) * (quenchedPressure N μ β - t))}

/-- The single global denominator event in the Gibbs normalization step. -/
def pressureUpperTailEvent (N : ℕ) (μ : FiniteMixture) (β t : ℝ) :
    Set (Disorder N μ.maxDegree) :=
  {J | quenchedPressure N μ β + t < Real.log (mixturePartition μ β J) / (N : ℝ)}

/-- The Gibbs denominator is exposed once, before the slab net union bound. -/
theorem fixedSlabLowerTailEvent_subset_unnormalized {N j : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β ρ t : ℝ) (σ : Fin j → Vector N) :
    fixedSlabLowerTailEvent μ β ρ t σ ⊆
      pressureUpperTailEvent N μ β (t / 2) ∪
        fixedSlabPartitionLowerTailEvent μ β ρ (t / 2) σ := by
  intro J hbad
  by_contra hnot
  have hupper : Real.log (mixturePartition μ β J) / (N : ℝ) ≤
      quenchedPressure N μ β + t / 2 := by
    exact le_of_not_gt fun h => hnot (Or.inl h)
  have hlower : Real.exp ((N : ℝ) * (quenchedPressure N μ β - t / 2)) ≤
      fixedSlabPartition μ β ρ J σ := by
    exact le_of_not_gt fun h => hnot (Or.inr h)
  have hZ := mixturePartition_pos hN μ β J
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hZupper : mixturePartition μ β J ≤
      Real.exp ((N : ℝ) * (quenchedPressure N μ β + t / 2)) := by
    have hh := (div_le_iff₀ hNr).mp hupper
    calc
      _ = Real.exp (Real.log (mixturePartition μ β J)) := (Real.exp_log hZ).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [hh])
  have hB : MeasurableSet {y : Vector N | ∀ i, |overlap y (σ i)| < ρ} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt
      (by unfold overlap; fun_prop) measurable_const
  have hmass : Real.exp (-t * (N : ℝ)) ≤
      (gibbsLaw N β (fieldOfMixture μ J)).real
        {y | ∀ i, |overlap y (σ i)| < ρ} := by
    rw [gibbsLaw_real_eq_partitionOn_div hN β
      (fieldOfMixture_contDiff μ J).continuous hB]
    change Real.exp (-t * (N : ℝ)) ≤ fixedSlabPartition μ β ρ J σ /
      mixturePartition μ β J
    calc
      _ = Real.exp ((N : ℝ) * (quenchedPressure N μ β - t / 2)) /
          Real.exp ((N : ℝ) * (quenchedPressure N μ β + t / 2)) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      _ ≤ Real.exp ((N : ℝ) * (quenchedPressure N μ β - t / 2)) /
          mixturePartition μ β J :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hZ hZupper
      _ ≤ _ := div_le_div_of_nonneg_right hlower hZ.le
  exact (not_lt_of_ge hmass) hbad

/-- The coefficient loss in replacing arbitrary directions by a frame is
at most the square root of the frame size. -/
theorem sum_abs_le_sqrt_of_sum_sq_eq_one {r : ℕ} (a : Fin r → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    ∑ i, |a i| ≤ Real.sqrt (r : ℝ) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin r => |a i|) (fun _ : Fin r => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ha, one_mul] at hCS
  apply (sq_le_sq₀ (Finset.sum_nonneg fun i _ => abs_nonneg (a i))
    (Real.sqrt_nonneg _)).mp
  simpa only [Real.sq_sqrt (Nat.cast_nonneg r)] using hCS

/-- A spherical vector represented in a spherical orthogonal frame has a
unit vector of coefficients, in the repository's radius `sqrt N` convention. -/
theorem sum_sq_eq_one_of_spherical_frame_rep {N r : ℕ} (hN : 0 < N)
    (e : Fin r → Vector N) (he : Orthonormal ℝ e)
    (σ : Vector N) (hσ : ‖σ‖ ^ 2 = (N : ℝ)) (a : Fin r → ℝ)
    (hrep : σ = ∑ i, a i • (Real.sqrt (N : ℝ) • e i)) :
    ∑ i, a i ^ 2 = 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hi := he.inner_sum a a Finset.univ
  have hn : ‖∑ i, a i • e i‖ ^ 2 = ∑ i, a i ^ 2 := by
    simpa [real_inner_self_eq_norm_sq, pow_two] using hi
  have hrep' : σ = Real.sqrt (N : ℝ) • (∑ i, a i • e i) := by
    rw [hrep, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [smul_smul]
    congr 1
    ring
  have hscaled : (N : ℝ) * (∑ i, a i ^ 2) = (N : ℝ) := by
    calc
      _ = ‖σ‖ ^ 2 := by
        rw [hrep', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
          Real.sq_sqrt hNr.le, hn]
      _ = (N : ℝ) := hσ
  nlinarith

/-- Every finite spherical tuple admits a spherical orthogonal frame with
at most as many directions, together with unit coordinate vectors. -/
theorem exists_spherical_frame_coordinates {N j : ℕ} (hN : 0 < N)
    (σ : Fin j → Vector N) (hσ : ∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) :
    ∃ r : ℕ, r ≤ j ∧ ∃ e : Fin r → Vector N, Orthonormal ℝ e ∧
      ∃ a : Fin j → Fin r → ℝ,
        (∀ i, σ i = ∑ l, a i l • (Real.sqrt (N : ℝ) • e l)) ∧
        (∀ i, ∑ l, a i l ^ 2 = 1) := by
  classical
  let V : Submodule ℝ (Vector N) := Submodule.span ℝ (Set.range σ)
  let r := Module.finrank ℝ V
  let b : OrthonormalBasis (Fin r) ℝ V := stdOrthonormalBasis ℝ V
  let e : Fin r → Vector N := fun l => (b l : Vector N)
  have he : Orthonormal ℝ e := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hr : r ≤ j := by
    calc
      r ≤ (Set.range σ).toFinset.card := finrank_span_le_card (Set.range σ)
      _ = Fintype.card (Set.range σ) := Set.toFinset_card _
      _ ≤ Fintype.card (Fin j) := Fintype.card_range_le σ
      _ = j := Fintype.card_fin j
  let v : Fin j → V := fun i => ⟨(Real.sqrt (N : ℝ))⁻¹ • σ i,
    V.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))⟩
  let a : Fin j → Fin r → ℝ := fun i l => b.repr (v i) l
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have hrep (i : Fin j) :
      σ i = ∑ l, a i l • (Real.sqrt (N : ℝ) • e l) := by
    have hb := congrArg (fun x : V => (x : Vector N)) (b.sum_repr (v i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hb
    change (∑ l, a i l • e l) = (v i : Vector N) at hb
    calc
      σ i = Real.sqrt (N : ℝ) • (v i : Vector N) := by
        dsimp only [v]
        rw [smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
      _ = Real.sqrt (N : ℝ) • (∑ l, a i l • e l) := by rw [hb]
      _ = _ := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro l _hl
        simp only [smul_smul]
        congr 1
        ring
  exact ⟨r, hr, e, he, a, hrep, fun i =>
    sum_sq_eq_one_of_spherical_frame_rep hN e he (σ i) (hσ i) (a i) (hrep i)⟩

/-- A normalized frame's exact coordinate identity supplies the `sqrt r`
loss in the source span argument. -/
theorem overlap_linear_combination_le {N r : ℕ}
    (y : Vector N) (frame : Fin r → Vector N) (a : Fin r → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (ha : ∑ i, a i ^ 2 = 1)
    (hslab : ∀ i, |overlap y (frame i)| ≤ η) :
    |overlap y (∑ i, a i • frame i)| ≤ Real.sqrt (r : ℝ) * η := by
  have heq : overlap y (∑ i, a i • frame i) =
      ∑ i, a i * overlap y (frame i) := by
    simp only [overlap, inner_sum, inner_smul_right, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [heq]
  calc
    |∑ i, a i * overlap y (frame i)| ≤
        ∑ i, |a i * overlap y (frame i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * η := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hslab i) (abs_nonneg _)
    _ = (∑ i, |a i|) * η := (Finset.sum_mul ..).symm
    _ ≤ Real.sqrt (r : ℝ) * η :=
      mul_le_mul_of_nonneg_right (sum_abs_le_sqrt_of_sum_sq_eq_one a ha) hη

/-- Uniform narrow frame slabs control every tuple represented by unit
coefficient vectors in that frame. This keeps the frame-size factor explicit. -/
theorem slab_subset_of_frame_coordinates {N j r : ℕ}
    (σ : Fin j → Vector N) (frame : Fin r → Vector N)
    (a : Fin j → Fin r → ℝ)
    (hrep : ∀ i, σ i = ∑ l, a i l • frame l)
    (ha : ∀ i, ∑ l, a i l ^ 2 = 1)
    {η ρ : ℝ} (hη : 0 ≤ η) (hwidth : Real.sqrt (r : ℝ) * η < ρ)
    (y : Vector N) (hslab : ∀ l, |overlap y (frame l)| ≤ η) :
    ∀ i, |overlap y (σ i)| < ρ := by
  intro i
  rw [hrep i]
  exact (overlap_linear_combination_le y frame (a i) hη (ha i) hslab).trans_lt hwidth

/-- A coordinate product of the physical sphere nets has entropy proportional
to the number of directions, with no dimension dependent loss. -/
theorem exists_spherical_tuple_net (N : ℕ) (hN : 0 < N) (j : ℕ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ (M : ℕ) (points : (Fin j → Fin M) → Fin j → Vector N),
      0 < M ∧
      (∀ a i, ‖points a i‖ ^ 2 = (N : ℝ)) ∧
      (∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
        ∃ a, ∀ i, ‖σ i - points a i‖ ≤ θ * Real.sqrt (N : ℝ)) ∧
      Real.log (Fintype.card (Fin j → Fin M) : ℝ) ≤
        (N : ℝ) * (j : ℝ) * Real.log (1 + 2 / θ) := by
  obtain ⟨M, p, hM, hp, hcover, hcard⟩ :=
    SourcePureCaptureReplicaNetGeometry.exists_physical_center_net N hN
      (Q := 1) zero_lt_one hθ
  simp only [Real.sqrt_one, mul_one] at hp hcover hcard
  refine ⟨M, fun a i => p (a i), hM, ?_, ?_, ?_⟩
  · intro a i
    rw [hp, Real.sq_sqrt (Nat.cast_nonneg N)]
  · intro σ hσ
    have hn (i : Fin j) : ‖σ i‖ = Real.sqrt (N : ℝ) := by
      apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [hσ, Real.sq_sqrt (Nat.cast_nonneg N)]
    choose a ha using fun i => hcover (σ i) (hn i)
    exact ⟨a, ha⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [Real.log_pow]
    calc
      (j : ℝ) * Real.log (M : ℝ) ≤
          (j : ℝ) * ((N : ℝ) * Real.log (1 + 2 / θ)) :=
        mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg j)
      _ = _ := by ring

/-- Moving a slab direction by `θ √N` changes its normalized overlap with
any spherical point by at most `θ`. -/
theorem overlap_sub_le_of_sphere_distance {N : ℕ} (hN : 0 < N)
    (y σ τ : Vector N) (hy : ‖y‖ ^ 2 = (N : ℝ)) {θ : ℝ}
    (hclose : ‖σ - τ‖ ≤ θ * Real.sqrt (N : ℝ)) :
    |overlap y σ - overlap y τ| ≤ θ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hyn : ‖y‖ = Real.sqrt (N : ℝ) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hy, Real.sq_sqrt hNr.le]
  have heq : overlap y σ - overlap y τ = inner ℝ y (σ - τ) / (N : ℝ) := by
    simp only [overlap, inner_sub_right, sub_div]
  rw [heq, abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  calc
    |inner ℝ y (σ - τ)| ≤ ‖y‖ * ‖σ - τ‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (N : ℝ) * (θ * Real.sqrt (N : ℝ)) := by
      rw [hyn]
      exact mul_le_mul_of_nonneg_left hclose (Real.sqrt_nonneg _)
    _ = θ * (Real.sqrt (N : ℝ)) ^ 2 := by ring
    _ = θ * (N : ℝ) := by rw [Real.sq_sqrt hNr.le]

/-- Strict slabs transfer through a tuple net after shrinking their width. -/
theorem slab_subset_of_tuple_distance {N j : ℕ} (hN : 0 < N)
    (σ τ : Fin j → Vector N) {θ η ρ : ℝ} (hwidth : θ + η ≤ ρ)
    (hclose : ∀ i, ‖σ i - τ i‖ ≤ θ * Real.sqrt (N : ℝ))
    (y : Vector N) (hy : ‖y‖ ^ 2 = (N : ℝ))
    (hslab : ∀ i, |overlap y (τ i)| < η) :
    ∀ i, |overlap y (σ i)| < ρ := by
  intro i
  have hdiff := overlap_sub_le_of_sphere_distance hN y (σ i) (τ i) hy (hclose i)
  calc
    |overlap y (σ i)| =
        |(overlap y (σ i) - overlap y (τ i)) + overlap y (τ i)| := by
      congr 1
      ring
    _ ≤
        |overlap y (σ i) - overlap y (τ i)| + |overlap y (τ i)| :=
      abs_add_le _ _
    _ < θ + η := add_lt_add_of_le_of_lt hdiff (hslab i)
    _ ≤ ρ := hwidth

/-- The continuum failure event is covered by finitely many fixed tuple
events. The Gibbs law's actual support supplies the sphere restriction. -/
theorem uniformSlabLowerTailEvent_subset_net {N j M : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β t : ℝ) {ρ η θ : ℝ} (hwidth : θ + η ≤ ρ)
    (points : (Fin j → Fin M) → Fin j → Vector N)
    (hcover : ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      ∃ a, ∀ i, ‖σ i - points a i‖ ≤ θ * Real.sqrt (N : ℝ)) :
    uniformSlabLowerTailEvent N j μ β ρ t ⊆
      ⋃ a, fixedSlabLowerTailEvent μ β η t (points a) := by
  intro J hJ
  classical
  simp only [uniformSlabLowerTailEvent, mem_ofPred_eq, not_forall, not_le] at hJ
  obtain ⟨σ, hsphere, _hblock, hbad⟩ := hJ
  obtain ⟨a, ha⟩ := hcover σ hsphere
  refine mem_iUnion.mpr ⟨a, ?_⟩
  let _ := gibbsLaw_probability hN β (fieldOfMixture_contDiff μ J).continuous
  have hν := gibbsLaw_support hN β (fieldOfMixture μ J)
  have hsub : ∀ᵐ y ∂gibbsLaw N β (fieldOfMixture μ J),
      y ∈ {y | ∀ i, |overlap y (points a i)| < η} →
        y ∈ {y | ∀ i, |overlap y (σ i)| < ρ} := by
    filter_upwards [hν] with y hy
    exact slab_subset_of_tuple_distance (by omega) σ (points a) hwidth ha y hy
  have hmono := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact lt_of_le_of_lt hmono hbad

/-- The corresponding outer probability bound does not require the uniform
failure event to be measurable. -/
theorem uniformSlabLowerTailProbability_le_net {N j M : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β t : ℝ) {ρ η θ : ℝ} (hwidth : θ + η ≤ ρ)
    (points : (Fin j → Fin M) → Fin j → Vector N)
    (hcover : ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      ∃ a, ∀ i, ‖σ i - points a i‖ ≤ θ * Real.sqrt (N : ℝ)) :
    uniformSlabLowerTailProbability N j μ β ρ t ≤
      ∑ a : Fin j → Fin M, (disorderLaw N μ.maxDegree).real
        (fixedSlabLowerTailEvent μ β η t (points a)) := by
  exact (measureReal_mono (uniformSlabLowerTailEvent_subset_net hN μ β t
    hwidth points hcover)).trans (measureReal_iUnion_fintype_le _)

/-- The uniform event has one global full-pressure failure event and a net
of unnormalized slab failures. The denominator event is never counted per point. -/
theorem uniformSlabLowerTailEvent_subset_unnormalized_net {N j M : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β t : ℝ) {ρ η θ : ℝ}
    (hwidth : θ + η ≤ ρ)
    (points : (Fin j → Fin M) → Fin j → Vector N)
    (hcover : ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      ∃ a, ∀ i, ‖σ i - points a i‖ ≤ θ * Real.sqrt (N : ℝ)) :
    uniformSlabLowerTailEvent N j μ β ρ t ⊆
      pressureUpperTailEvent N μ β (t / 2) ∪
        ⋃ a, fixedSlabPartitionLowerTailEvent μ β η (t / 2) (points a) := by
  intro J hJ
  obtain ⟨a, ha⟩ := mem_iUnion.mp
    (uniformSlabLowerTailEvent_subset_net hN μ β t hwidth points hcover hJ)
  rcases fixedSlabLowerTailEvent_subset_unnormalized hN μ β η t (points a) ha with
    hupper | hlower
  · exact Or.inl hupper
  · exact Or.inr (mem_iUnion.mpr ⟨a, hlower⟩)

/-- Outer probability version of the preceding decomposition. -/
theorem uniformSlabLowerTailProbability_le_unnormalized_net {N j M : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β t : ℝ) {ρ η θ : ℝ}
    (hwidth : θ + η ≤ ρ)
    (points : (Fin j → Fin M) → Fin j → Vector N)
    (hcover : ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      ∃ a, ∀ i, ‖σ i - points a i‖ ≤ θ * Real.sqrt (N : ℝ)) :
    uniformSlabLowerTailProbability N j μ β ρ t ≤
      (disorderLaw N μ.maxDegree).real (pressureUpperTailEvent N μ β (t / 2)) +
        ∑ a : Fin j → Fin M, (disorderLaw N μ.maxDegree).real
          (fixedSlabPartitionLowerTailEvent μ β η (t / 2) (points a)) := by
  calc
    _ ≤ (disorderLaw N μ.maxDegree).real
        (pressureUpperTailEvent N μ β (t / 2) ∪
          ⋃ a, fixedSlabPartitionLowerTailEvent μ β η (t / 2) (points a)) :=
      measureReal_mono (uniformSlabLowerTailEvent_subset_unnormalized_net
        hN μ β t hwidth points hcover)
    _ ≤ (disorderLaw N μ.maxDegree).real (pressureUpperTailEvent N μ β (t / 2)) +
        (disorderLaw N μ.maxDegree).real
          (⋃ a, fixedSlabPartitionLowerTailEvent μ β η (t / 2) (points a)) :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_iUnion_fintype_le _)

/-- Only the unnormalized slab lower rate pays for net entropy; full-pressure
upper concentration contributes one separate, possibly smaller, exponent. -/
theorem uniformSlabLowerTailProbability_le_exp_add_pressureUpper {N j : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β t c : ℝ) {ρ η θ : ℝ}
    (hθ : 0 < θ) (hwidth : θ + η ≤ ρ)
    (hfixed : ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      (disorderLaw N μ.maxDegree).real
        (fixedSlabPartitionLowerTailEvent μ β η (t / 2) σ) ≤
          Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ))) :
    uniformSlabLowerTailProbability N j μ β ρ t ≤
      (disorderLaw N μ.maxDegree).real (pressureUpperTailEvent N μ β (t / 2)) +
        Real.exp (-c * (N : ℝ)) := by
  obtain ⟨M, points, hM, hsphere, hcover, hcard⟩ :=
    exists_spherical_tuple_net N (by omega) j hθ
  have hcardpos : 0 < Fintype.card (Fin j → Fin M) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    positivity
  have hcardexp : (Fintype.card (Fin j → Fin M) : ℝ) ≤
      Real.exp ((N : ℝ) * (j : ℝ) * Real.log (1 + 2 / θ)) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hcardpos)).mp hcard
  have hsum : (∑ a : Fin j → Fin M, (disorderLaw N μ.maxDegree).real
      (fixedSlabPartitionLowerTailEvent μ β η (t / 2) (points a))) ≤
      Real.exp (-c * (N : ℝ)) := by
    calc
      _ ≤ ∑ _a : Fin j → Fin M,
          Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ)) :=
        Finset.sum_le_sum fun a _ => hfixed (points a) (hsphere a)
      _ = (Fintype.card (Fin j → Fin M) : ℝ) *
          Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ)) := by simp
      _ ≤ Real.exp ((N : ℝ) * (j : ℝ) * Real.log (1 + 2 / θ)) *
          Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact (uniformSlabLowerTailProbability_le_unnormalized_net hN μ β t hwidth
    points hcover).trans (add_le_add le_rfl hsum)

/-- Arbitrary rate lower tails absorb the exponential covering entropy.
The net threshold and its entropy are fixed before the dimension. -/
theorem uniformSlabLowerTailProbability_le_exp_of_fixed {N j : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β t c : ℝ) {ρ η θ : ℝ}
    (hθ : 0 < θ) (hwidth : θ + η ≤ ρ)
    (hfixed : ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
      (disorderLaw N μ.maxDegree).real (fixedSlabLowerTailEvent μ β η t σ) ≤
        Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ))) :
    uniformSlabLowerTailProbability N j μ β ρ t ≤ Real.exp (-c * (N : ℝ)) := by
  obtain ⟨M, points, hM, hsphere, hcover, hcard⟩ :=
    exists_spherical_tuple_net N (by omega) j hθ
  have hcardpos : 0 < Fintype.card (Fin j → Fin M) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    positivity
  have hcardexp : (Fintype.card (Fin j → Fin M) : ℝ) ≤
      Real.exp ((N : ℝ) * (j : ℝ) * Real.log (1 + 2 / θ)) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hcardpos)).mp hcard
  calc
    _ ≤ ∑ a : Fin j → Fin M, (disorderLaw N μ.maxDegree).real
        (fixedSlabLowerTailEvent μ β η t (points a)) :=
      uniformSlabLowerTailProbability_le_net hN μ β t hwidth points hcover
    _ ≤ ∑ _a : Fin j → Fin M,
        Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ)) :=
      Finset.sum_le_sum fun a _ => hfixed (points a) (hsphere a)
    _ = (Fintype.card (Fin j → Fin M) : ℝ) *
        Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ)) := by simp
    _ ≤ Real.exp ((N : ℝ) * (j : ℝ) * Real.log (1 + 2 / θ)) *
        Real.exp (-(c + (j : ℝ) * Real.log (1 + 2 / θ)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardexp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Dimension uniform fixed tuple tails imply the actual uniform slab tails.
The mesh is half the target slab width and hence is chosen before dimension. -/
theorem uniformSlabLowerTail_arbitrary_rate_of_fixed (μ : FiniteMixture)
    (β : ℝ) (j : ℕ)
    (hfixed : ∀ η t c : ℝ, 0 < η → 0 < t → 0 < c →
      ∀ᶠ N : ℕ in atTop, ∀ σ : Fin j → Vector N,
        (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
          (disorderLaw N μ.maxDegree).real (fixedSlabLowerTailEvent μ β η t σ) ≤
            Real.exp (-c * (N : ℝ)))
    {ρ t c : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      uniformSlabLowerTailProbability N j μ β ρ t ≤ Real.exp (-c * (N : ℝ)) := by
  have hhalf : 0 < ρ / 2 := by linarith
  have hH : 0 ≤ (j : ℝ) * Real.log (1 + 2 / (ρ / 2)) := by
    apply mul_nonneg (Nat.cast_nonneg j)
    apply Real.log_nonneg
    have : 0 < 2 / (ρ / 2) := div_pos (by norm_num) hhalf
    linarith
  filter_upwards [hfixed (ρ / 2) t
    (c + (j : ℝ) * Real.log (1 + 2 / (ρ / 2))) hhalf ht (by linarith),
    eventually_ge_atTop (1 : ℕ)] with N hpoint hN
  exact uniformSlabLowerTailProbability_le_exp_of_fixed hN μ β t c hhalf
    (by linarith) hpoint

/-- There is no bad event before the first replica is drawn. -/
theorem uniformSlabLowerTailProbability_zero {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β ρ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    uniformSlabLowerTailProbability N 0 μ β ρ t = 0 := by
  have he : Real.exp (-t * (N : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Nat.cast_nonneg N))
  have hempty : uniformSlabLowerTailEvent N 0 μ β ρ t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro J hJ
    apply hJ
    intro σ _hsphere _hblock
    let _ := gibbsLaw_probability hN β (fieldOfMixture_contDiff μ J).continuous
    simpa using he
  rw [uniformSlabLowerTailProbability, hempty, measureReal_empty]

/-- The finite sequential replica union preserves every exponential rate.
The extra unit of rate pays for the fixed replica count. -/
theorem zero_blockLowerTail_arbitrary_rate_of_uniformSlabs {k : ℕ}
    (hk : 1 ≤ k) (μ : FiniteMixture) (β ρ : ℝ)
    (hslab : ∀ j : ℕ, j < k → ∀ t c : ℝ, 0 < t → 0 < c →
      ∀ᶠ N : ℕ in atTop,
        uniformSlabLowerTailProbability N j μ β ρ t ≤ Real.exp (-c * (N : ℝ)))
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      blockLowerTailProbability N k μ β 0 ρ ε ≤ Real.exp (-c * (N : ℝ)) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfin : ∀ᶠ N : ℕ in atTop, ∀ j : Fin k,
      uniformSlabLowerTailProbability N j.val μ β ρ (ε / (k : ℝ)) ≤
        Real.exp (-(c + 1) * (N : ℝ)) :=
    Filter.eventually_all.mpr fun j =>
      hslab j.val j.isLt (ε / (k : ℝ)) (c + 1) (div_pos hε hkR) (by linarith)
  filter_upwards [hfin, eventually_ge_atTop k, eventually_ge_atTop (1 : ℕ)]
    with N hpoint hNk hN
  have hNkR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNk
  have hkexp : (k : ℝ) ≤ Real.exp (N : ℝ) :=
    hNkR.trans (by linarith [Real.add_one_le_exp (N : ℝ)])
  calc
    _ ≤ ∑ j : Fin k,
        uniformSlabLowerTailProbability N j.val μ β ρ (ε / (k : ℝ)) :=
      zero_blockLowerTailProbability_le_uniformSlabs hN hk μ β ρ ε
    _ ≤ ∑ _j : Fin k, Real.exp (-(c + 1) * (N : ℝ)) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = (k : ℝ) * Real.exp (-(c + 1) * (N : ℝ)) := by simp
    _ ≤ Real.exp (N : ℝ) * Real.exp (-(c + 1) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hkexp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The practical normalized Gibbs version needs only some positive slab
rate. A common positive rate survives the finite sequential union bound. -/
theorem zero_blockLowerTail_positive_rate_of_uniformSlabs {k : ℕ}
    (hk : 1 ≤ k) (μ : FiniteMixture) (β ρ : ℝ)
    (hslab : ∀ j : ℕ, j < k → ∀ t : ℝ, 0 < t →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
        uniformSlabLowerTailProbability N j μ β ρ t ≤ Real.exp (-c * (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      blockLowerTailProbability N k μ β 0 ρ ε ≤ Real.exp (-c * (N : ℝ)) := by
  classical
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  choose rate hrate htail using fun j : Fin k =>
    hslab j.val j.isLt (ε / (k : ℝ)) (div_pos hε hkR)
  let S : Finset ℝ := Finset.univ.image rate
  have hS : S.Nonempty := ⟨rate ⟨0, by omega⟩,
    Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩⟩
  let d : ℝ := S.min' hS
  have hd : 0 < d := by
    obtain ⟨j, _hj, heq⟩ := Finset.mem_image.mp (S.min'_mem hS)
    change 0 < S.min' hS
    rw [← heq]
    exact hrate j
  have hdle (j : Fin k) : d ≤ rate j :=
    S.min'_le _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hhalf : 0 < d / 2 := by linarith
  refine ⟨d / 2, hhalf, ?_⟩
  have hfin : ∀ᶠ N : ℕ in atTop, ∀ j : Fin k,
      uniformSlabLowerTailProbability N j.val μ β ρ (ε / (k : ℝ)) ≤
        Real.exp (-d * (N : ℝ)) := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [htail j] with N hN
    apply hN.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (hdle j)) (Nat.cast_nonneg N)
  have hsize : ∀ᶠ N : ℕ in atTop, (k : ℝ) / (d / 2) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hfin, hsize, eventually_ge_atTop (1 : ℕ)] with N hpoint hlarge hN
  have hkexp : (k : ℝ) ≤ Real.exp (d / 2 * (N : ℝ)) := by
    have hlarge' : (k : ℝ) ≤ (N : ℝ) * (d / 2) := (div_le_iff₀ hhalf).mp hlarge
    linarith [Real.add_one_le_exp (d / 2 * (N : ℝ))]
  calc
    _ ≤ ∑ j : Fin k,
        uniformSlabLowerTailProbability N j.val μ β ρ (ε / (k : ℝ)) :=
      zero_blockLowerTailProbability_le_uniformSlabs hN hk μ β ρ ε
    _ ≤ ∑ _j : Fin k, Real.exp (-d * (N : ℝ)) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = (k : ℝ) * Real.exp (-d * (N : ℝ)) := by simp
    _ ≤ Real.exp (d / 2 * (N : ℝ)) * Real.exp (-d * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hkexp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SlowEquilibration.LiteratureSubagBandLowerTails
