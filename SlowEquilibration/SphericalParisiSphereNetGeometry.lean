-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalParisiGroundRSUpper
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Data.Fintype.EquivFin

/-! Actual internal Euclidean unit-sphere nets, with their exponential
cardinality proved by disjoint Haar-volume balls. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory Set Metric Module
open SphericalAging.FiniteModel PureTensorJetBounds
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem separated_unit_ball_card_le (s : Finset (Vector N)) {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ x ∈ s,‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s,∀ y ∈ s,x ≠ y → ε ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 / ε)^N := by
  let μ : Measure (Vector N) := Measure.addHaar
  let δ : ℝ := ε / 2
  let ρ : ℝ := 1 + δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ x ∈ s,ball x δ
  have hd : Set.Pairwise (s : Set (Vector N)) (fun x y => Disjoint (ball x δ) (ball y δ)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa only [δ,add_halves] using hsep x hx y hy hxy
  have hsub : A ⊆ ball (0 : Vector N) ρ := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp [ρ]
    linarith [hs x hx]
  have hv : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ^N) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^N) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ x ∈ s,ball x δ from rfl,measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ,finrank_euclideanSpace_fin,Finset.sum_const,nsmul_eq_mul,mul_assoc]
      _ ≤ μ (ball (0 : Vector N) ρ) := measure_mono hsub
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ hρ,finrank_euclideanSpace_fin]
  have hv' : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ^N) ≤ ENNReal.ofReal (ρ^N) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).mp hv
  have hr : (s.card : ℝ) * δ^N ≤ ρ^N := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le N) hv'
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (pow_nonneg hδ.le N)] using h
  calc
    _ ≤ ρ^N / δ^N := (le_div_iff₀ (pow_pos hδ N)).mpr hr
    _ = (ρ / δ)^N := (div_pow _ _ _).symm
    _ = _ := by
      congr 1
      dsimp [ρ,δ]
      field_simp
      ring

theorem exists_unitSphere_finset_net (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (Vector N),s.Nonempty ∧
      (∀ y ∈ s,‖y‖ = 1) ∧
      (∀ x : UnitSphere N,∃ y ∈ s,‖x.val - y‖ ≤ ε) ∧
      (s.card : ℝ) ≤ (1 + 2 / ε)^N := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  let A : Set (Vector N) := sphere 0 1
  have he : 0 < e := hε
  obtain ⟨C,hCA,hCfin,hCcover⟩ := exists_finite_isCover_of_isCompact
    (ε := e / 2) (div_pos he (by norm_num)).ne' (isCompact_sphere (0 : Vector N) 1)
  have hpack : packingNumber e A ≠ ⊤ := by
    have hb := (packingNumber_two_mul_le_externalCoveringNumber (e / 2) A).trans
      hCcover.externalCoveringNumber_le_encard
    rw [show (2 : ℝ≥0) * (e / 2) = e by ring] at hb
    exact ne_top_of_le_ne_top (encard_ne_top_iff.mpr hCfin) hb
  let S := maximalSeparatedSet e A
  have hSfin : S.Finite := encard_ne_top_iff.mp (by
    rw [show S = maximalSeparatedSet e A from rfl,encard_maximalSeparatedSet hpack]
    exact hpack)
  let s := hSfin.toFinset
  have hSs (y : Vector N) : y ∈ s ↔ y ∈ S := hSfin.mem_toFinset
  have hsubset : S ⊆ A := maximalSeparatedSet_subset
  have hcover : IsCover e A S := isCover_maximalSeparatedSet hpack
  have hseparated : IsSeparated e S := isSeparated_maximalSeparatedSet
  have hunit (y : Vector N) (hy : y ∈ s) : ‖y‖ = 1 := by
    simpa only [A,mem_sphere,dist_zero_right] using hsubset ((hSs y).mp hy)
  have hclose (x : UnitSphere N) : ∃ y ∈ s,‖x.val - y‖ ≤ ε := by
    obtain ⟨y,hy,hxy⟩ := hcover x.property
    refine ⟨y,(hSs y).mpr hy,?_⟩
    change edist x.val y ≤ (e : ℝ≥0∞) at hxy
    rw [edist_dist,ENNReal.ofReal_le_coe] at hxy
    change dist x.val y ≤ ε at hxy
    simpa only [dist_eq_norm] using hxy
  obtain ⟨y,hy,_⟩ := hclose (Classical.choice inferInstance)
  refine ⟨s,⟨y,hy⟩,hunit,hclose,separated_unit_ball_card_le s hε (fun z hz => (hunit z hz).le) ?_⟩
  intro x hx y hy hxy
  have h := hseparated ((hSs x).mp hx) ((hSs y).mp hy) hxy
  have hd : ε < ‖x - y‖ := by
    change (e : ℝ≥0∞) < edist x y at h
    rw [edist_dist,ENNReal.coe_lt_ofReal] at h
    change ε < dist x y at h
    simpa only [dist_eq_norm] using h
  exact hd.le

/-- An actual finite unit-sphere reference with explicit exponential
cardinality; no net or cardinality bound is supplied as data. -/
theorem exists_unitSphere_net (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (points : Fin k → UnitSphere N),0 < k ∧
      (∀ x : UnitSphere N,∃ j,‖x.val - (points j).val‖ ≤ ε) ∧
      Real.log (k : ℝ) ≤ (N : ℝ) * Real.log (1 + 2 / ε) := by
  classical
  obtain ⟨s,hs,hunit,hclose,hcard⟩ := exists_unitSphere_finset_net hN hε
  let points : Fin s.card → UnitSphere N := fun j =>
    ⟨(s.equivFin.symm j).val,by simpa only [mem_sphere,dist_zero_right] using hunit _ (s.equivFin.symm j).property⟩
  refine ⟨s.card,points,Finset.card_pos.mpr hs,?_,?_⟩
  · intro x
    obtain ⟨y,hy,hxy⟩ := hclose x
    refine ⟨s.equivFin ⟨y,hy⟩,?_⟩
    simpa only [points,Equiv.symm_apply_apply] using hxy
  · have hk : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
    calc
      _ ≤ Real.log ((1 + 2 / ε)^N) := Real.log_le_log hk hcard
      _ = _ := by rw [Real.log_pow]

end SlowEquilibration.SphericalParisiSphereNet
