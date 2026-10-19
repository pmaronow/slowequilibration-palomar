module

public import SphericalAging.StoppedVectorIto

public section

/-! First closed-level hitting in the actual filtration.

All-path continuity makes the event of reaching a closed level by time `s`
detectable from countably many past samples with arbitrarily small level
tolerance. This proves the stopping-time property directly, without right
continuity of the filtration. The rule is capped at the given horizon.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ClosedHitStopping
open AdaptedContinuous
set_option maxHeartbeats 1000000

@[expose] def closedHitSet {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω) : Set ℝ≥0 :=
  (Icc 0 T ∩ {s | R ≤ Z s ω}) ∪ {T}

@[expose] def firstClosedHit {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω) : ℝ≥0 :=
  sInf (closedHitSet Z T R ω)

lemma closedHitSet_nonempty {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω) :
    (closedHitSet Z T R ω).Nonempty := ⟨T, Or.inr rfl⟩

lemma closedHitSet_isCompact {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω)
    (hZ : Continuous (fun s => Z s ω)) : IsCompact (closedHitSet Z T R ω) := by
  exact (isCompact_Icc.inter_right (isClosed_Ici.preimage hZ)).union isCompact_singleton

theorem firstClosedHit_isLeast {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω)
    (hZ : Continuous (fun s => Z s ω)) : IsLeast (closedHitSet Z T R ω) (firstClosedHit Z T R ω) :=
  (closedHitSet_isCompact Z T R ω hZ).isLeast_sInf (closedHitSet_nonempty Z T R ω)

theorem firstClosedHit_le {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω)
    (hZ : Continuous (fun s => Z s ω)) : firstClosedHit Z T R ω ≤ T :=
  (firstClosedHit_isLeast Z T R ω hZ).2 (Or.inr rfl)

theorem firstClosedHit_le_iff {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω)
    (hZ : Continuous (fun s => Z s ω)) (s : ℝ≥0) :
    firstClosedHit Z T R ω ≤ s ↔ T ≤ s ∨ ∃ u ≤ s, R ≤ Z u ω := by
  have hl := firstClosedHit_isLeast Z T R ω hZ
  constructor
  · intro hs
    rcases hl.1 with h | h
    · exact Or.inr ⟨_, hs, h.2⟩
    · exact Or.inl (h ▸ hs)
  · rintro (h | ⟨u, hu, hZu⟩)
    · exact (firstClosedHit_le Z T R ω hZ).trans h
    · by_cases hTs : T ≤ s
      · exact (firstClosedHit_le Z T R ω hZ).trans hTs
      · exact (hl.2 (Or.inl ⟨⟨bot_le, hu.trans (le_of_not_ge hTs)⟩, hZu⟩)).trans hu

theorem exists_level_iff_countable_samples {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ)
    (R : ℝ) (ω : Ω) (hZ : Continuous (fun s => Z s ω)) (s : ℝ≥0) :
    (∃ u ≤ s, R ≤ Z u ω) ↔ ∀ m : ℕ, ∃ n k : ℕ,
      R - 1 / ((m : ℝ) + 1) < Z (min (gridTime n k) s) ω := by
  constructor
  · rintro ⟨u, hu, hRu⟩ m
    have ht := hZ.continuousAt.tendsto.comp (tendsto_pastGrid u)
    have hm : R - 1 / ((m : ℝ) + 1) < Z u ω := by
      have hh : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_nhds hm)).exists
    refine ⟨n, ⌊u * (n+1)⌋₊, ?_⟩
    have hle : gridTime n ⌊u * (n+1)⌋₊ ≤ s := (pastGrid_le u n).trans hu
    rw [min_eq_left hle]
    exact hn
  · intro hsamples
    obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Icc (0 : ℝ≥0) s).Nonempty from ⟨0, bot_le, bot_le⟩) hZ.continuousOn
    have hle (m : ℕ) : R - 1 / ((m : ℝ) + 1) ≤ Z u ω := by
      obtain ⟨n, k, hnk⟩ := hsamples m
      exact hnk.le.trans (hmax ⟨bot_le, min_le_right _ _⟩)
    have ht : Tendsto (fun m : ℕ => R - 1 / ((m : ℝ) + 1)) atTop (𝓝 R) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact ⟨u, hu.2, le_of_tendsto ht (.of_forall hle)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem measurableSet_exists_level (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted 𝓕 Z)
    (hZc : ∀ ω, Continuous (fun s => Z s ω)) (R : ℝ) (s : ℝ≥0) :
    MeasurableSet[𝓕 s] {ω | ∃ u ≤ s, R ≤ Z u ω} := by
  have he : {ω | ∃ u ≤ s, R ≤ Z u ω} =
      ⋂ m : ℕ, ⋃ n : ℕ, ⋃ k : ℕ, {ω | R - 1 / ((m : ℝ) + 1) < Z (min (gridTime n k) s) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    exact exists_level_iff_countable_samples Z R ω (hZc ω) s
  rw [he]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_lt measurable_const
    ((hZa (min (gridTime n k) s)).mono (𝓕.mono (min_le_right _ _))).measurable

/-- Actual closed hitting is a stopping time in the given filtration;
no right-continuity hypothesis is required. -/
theorem isStoppingTime_firstClosedHit (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted 𝓕 Z)
    (hZc : ∀ ω, Continuous (fun s => Z s ω)) (T : ℝ≥0) (R : ℝ) :
    IsStoppingTime 𝓕 (fun ω => (firstClosedHit Z T R ω : WithTop ℝ≥0)) := by
  intro s
  have he : {ω | (firstClosedHit Z T R ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} =
      (if T ≤ s then univ else {ω | ∃ u ≤ s, R ≤ Z u ω}) := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, firstClosedHit_le_iff Z T R ω (hZc ω) s]
    split_ifs <;> simp_all
  rw [he]
  split_ifs
  · exact MeasurableSet.univ
  · exact measurableSet_exists_level Z hZa hZc R s

omit [MeasurableSpace Ω] in
theorem below_level_before_hit (Z : ℝ≥0 → Ω → ℝ)
    (hZc : ∀ ω, Continuous (fun s => Z s ω)) (T : ℝ≥0) (R : ℝ)
    (ω : Ω) (s : ℝ≥0) (hs : s < firstClosedHit Z T R ω) : Z s ω < R := by
  by_contra h
  have hmem : s ∈ closedHitSet Z T R ω := Or.inl
    ⟨⟨bot_le, hs.le.trans (firstClosedHit_le Z T R ω (hZc ω))⟩, le_of_not_gt h⟩
  exact not_lt_of_ge ((firstClosedHit_isLeast Z T R ω (hZc ω)).2 hmem) hs

omit [MeasurableSpace Ω] in
theorem level_le_upTo_hit (Z : ℝ≥0 → Ω → ℝ)
    (hZc : ∀ ω, Continuous (fun s => Z s ω)) (T : ℝ≥0) (R : ℝ)
    (hinitial : ∀ ω, Z 0 ω ≤ R) (ω : Ω) (s : ℝ≥0)
    (hs : s ≤ firstClosedHit Z T R ω) : Z s ω ≤ R := by
  by_cases hzero : firstClosedHit Z T R ω = 0
  · have hs0 : s = 0 := le_antisymm (hzero ▸ hs) bot_le
    simpa only [hs0] using hinitial ω
  · have hn : (Iio (firstClosedHit Z T R ω)).Nonempty :=
      ⟨(0 : ℝ≥0), lt_of_le_of_ne (α := ℝ≥0) bot_le (Ne.symm hzero)⟩
    have hc : IsClosed {u | Z u ω ≤ R} := isClosed_Iic.preimage (hZc ω)
    have hsubset : Iio (firstClosedHit Z T R ω) ⊆ {u | Z u ω ≤ R} :=
      fun u hu => (below_level_before_hit Z hZc T R ω u hu).le
    exact (closure_minimal hsubset hc) (by simpa only [closure_Iio' hn, mem_Iic] using hs)

@[expose] def radiusHit {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N) (T R : ℝ≥0) : Ω → ℝ≥0 :=
  firstClosedHit (fun t ω => ‖X t ω‖) T R

@[expose] def stoppedState {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N) (τ : Ω → ℝ≥0) :
    ℝ≥0 → Ω → HardSphereDynamics.State N := fun s ω => X (min s (τ ω)) ω

theorem isStoppingTime_radiusHit {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ ω, Continuous (fun t => X t ω)) (T R : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => (radiusHit X T R ω : WithTop ℝ≥0)) :=
  isStoppingTime_firstClosedHit (fun t ω => ‖X t ω‖) (fun t => (hXa t).norm)
    (fun ω => (hXc ω).norm) T R

omit [MeasurableSpace Ω] in
theorem radiusHit_le {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (T R : ℝ≥0) (ω : Ω) : radiusHit X T R ω ≤ T :=
  firstClosedHit_le (fun t ω => ‖X t ω‖) T R ω ((hXc ω).norm)

omit [MeasurableSpace Ω] in
theorem stoppedState_continuous {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (τ : Ω → ℝ≥0) (ω : Ω) :
    Continuous (fun s => stoppedState X τ s ω) :=
  (hXc ω).comp (continuous_id.min continuous_const)

omit [MeasurableSpace Ω] in
theorem stoppedState_eq_stoppedProcess {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (τ : Ω → ℝ≥0) : stoppedState X τ = stoppedProcess X (fun ω => (τ ω : WithTop ℝ≥0)) := by
  funext s ω
  unfold stoppedState stoppedProcess
  rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

theorem stoppedState_stronglyAdapted {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ ω, Continuous (fun t => X t ω)) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) : StronglyAdapted 𝓕 (stoppedState X τ) := by
  rw [stoppedState_eq_stoppedProcess]
  exact hXa.stoppedProcess hXc hτ

omit [MeasurableSpace Ω] in
/-- The actual continuously stopped state has a deterministic radius bound
on all times and all paths, including the hitting endpoint. -/
theorem stoppedState_radius_bound {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (T R : ℝ≥0)
    (hinitial : ∀ ω, ‖X 0 ω‖ ≤ R) (s : ℝ≥0) (ω : Ω) :
    ‖stoppedState X (radiusHit X T R) s ω‖ ≤ R :=
  level_le_upTo_hit (fun t ω => ‖X t ω‖) (fun ω => (hXc ω).norm) T R hinitial ω
    (min s (radiusHit X T R ω)) (min_le_right _ _)

omit [MeasurableSpace Ω] in
theorem level_eq_at_hit (Z : ℝ≥0 → Ω → ℝ)
    (hZc : ∀ ω, Continuous (fun s => Z s ω)) (T : ℝ≥0) (R : ℝ)
    (hinitial : ∀ ω, Z 0 ω ≤ R) (ω : Ω) (hT : firstClosedHit Z T R ω < T) :
    Z (firstClosedHit Z T R ω) ω = R := by
  apply le_antisymm
  · exact level_le_upTo_hit Z hZc T R hinitial ω _ le_rfl
  · rcases (firstClosedHit_isLeast Z T R ω (hZc ω)).1 with h | h
    · exact h.2
    · exact False.elim ((ne_of_lt hT) h)

omit [MeasurableSpace Ω] in
theorem radius_eq_at_hit {N : ℕ} (X : ℝ≥0 → Ω → HardSphereDynamics.State N)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (T R : ℝ≥0)
    (hinitial : ∀ ω, ‖X 0 ω‖ ≤ R) (ω : Ω) (hT : radiusHit X T R ω < T) :
    ‖X (radiusHit X T R ω) ω‖ = R :=
  level_eq_at_hit (fun t ω => ‖X t ω‖) (fun ω => (hXc ω).norm) T R hinitial ω hT

end SphericalAging.ClosedHitStopping
