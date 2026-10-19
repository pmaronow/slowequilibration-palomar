-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDoubleLatitudeWindows

/-! A good codimension-two latitude partition gives a genuine positive
volume restricted partition lower, from two actual coarea formulas. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalNestedLatitude
open MeasureTheory Set Filter Metric
open SphericalModel
open scoped Topology
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Deterministic actual double-latitude thickening. The dimension threshold
depends only on the two central latitudes, open outer band, temperature,
gradient bound, and tolerance; it is uniform in H, both centers, and B. -/
theorem nestedLatitude_partitionOn_eventually_lower {r₀ t₀ β K ε : ℝ}
    (hr₀ : |r₀|<1) (ht₀ : |t₀|<1) (hK : 0 ≤ K) (hε : 0<ε)
    {A : Set ℝ} (hA : IsOpen A) (hrA : r₀∈A) :
    ∀ᶠ n : ℕ in atTop,∀ (H : Vector (n+2) → ℝ),Differentiable ℝ H →
      (∀ x ∈ closedBall 0 (Real.sqrt (n+2:ℕ)),‖fderiv ℝ H x‖ ≤ K*Real.sqrt (n+2:ℕ)) →
      ∀ (w : Vector (n+2)),‖w‖^2=(n+2:ℕ) → ∀ (y : Vector (n+1)),‖y‖^2=(n+1:ℕ) → ∀ (B : ℝ),
      B ≤ Real.log (partition n β (fun z => H (nestedLatitude w y r₀ t₀ z)))/((n+2:ℕ):ℝ) →
      Real.exp (((n+2:ℕ):ℝ)*(B+(Real.log (1-r₀^2)+Real.log (1-t₀^2))/2-ε)) ≤
        partitionOn β H (overlapRegion w A) := by
  have hη : 0<ε/4 := by positivity
  obtain ⟨wr,hwr,hrlo,hrhi,hrsub,hrcost⟩ := exists_latitude_window (β := β) (K := K) hr₀ hη hA hrA
  obtain ⟨wt,hwt,htlo,hthi,htsub,htcost⟩ := exists_latitude_window (β := β) (K := K) ht₀ hη isOpen_univ (mem_univ t₀)
  have houter := coreBand_partition_eventually_ge hwr hrlo hrhi hη
  have hinner := coreBand_partition_eventually_ge hwt htlo hthi hη
  have houter' : ∀ᶠ n : ℕ in atTop,∀ (β' : ℝ) (H : Vector (n+2) → ℝ),Continuous H →
      ∀ (u : Vector (n+2)),‖u‖^2=(n+2:ℕ) → ∀ (M : ℝ),
      (∀ r ∈ Icc (r₀-wr) (r₀+wr),M ≤ latitudePartitionProfile (n+1) β' H u r) →
      Real.exp (((n+2:ℕ):ℝ)*(M-ε/4)) ≤ partitionOn β' H (coreBand u r₀ wr) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using (tendsto_add_atTop_nat 1).eventually houter
  filter_upwards [hinner,houter',eventually_ge_atTop 2] with n hinner houter hn
  intro H hH hgrad w hw y hy B hB
  have hn1 : 1≤n := by omega
  have hN : (0:ℝ)<(n+2:ℕ) := by positivity
  have hM : (0:ℝ)<(n+1:ℕ) := by positivity
  have hBM : ((n+2:ℕ):ℝ)*B ≤ Real.log (partition n β (fun z => H (nestedLatitude w y r₀ t₀ z))) :=
    by simpa only [mul_comm] using (le_div_iff₀ hN).mp hB
  have hprof : ∀ r ∈ Icc (r₀-wr) (r₀+wr),
      B+(Real.log (1-r₀^2)+Real.log (1-t₀^2))/2-3*ε/4 ≤ latitudePartitionProfile (n+1) β H w r := by
    intro r hr
    have hra : |r|<1 := abs_lt.mpr ⟨hrlo.trans_le hr.1,hr.2.trans_lt hrhi⟩
    let Hr : Vector (n+1) → ℝ := fun x => H (latitudeMap w (latitudeFrameAt w) r x)
    have hHr : Continuous Hr := hH.continuous.comp (latitudeMap_continuous _ _ _)
    let L := B-4*|β| *K*Real.sqrt |r-r₀|+Real.log (1-t₀^2)/2-ε/4
    have hinnerProf : ∀ t ∈ Icc (t₀-wt) (t₀+wt),
        (((n+2:ℕ):ℝ)/((n+1:ℕ):ℝ))*L ≤ latitudePartitionProfile n β Hr y t := by
      intro t ht
      have hta : |t|<1 := abs_lt.mpr ⟨htlo.trans_le ht.1,ht.2.trans_lt hthi⟩
      let D := 4*|β| *K*((n+2:ℕ):ℝ)*(Real.sqrt |r-r₀|+Real.sqrt |t-t₀|)
      have hpoint (z : Vector n) (hz : ‖z‖^2=(n:ℝ)) :
          β*H (nestedLatitude w y r₀ t₀ z) ≤ β*H (nestedLatitude w y r t z)+D := by
        have hm := nestedLatitude_field_modulus hn1 hH hK hgrad w hw y hy hra.le hr₀.le hta.le ht₀.le z hz
        have hmul := mul_le_mul_of_nonneg_left hm (abs_nonneg β)
        have hh := neg_le_abs (β*(H (nestedLatitude w y r t z)-H (nestedLatitude w y r₀ t₀ z)))
        rw [abs_mul] at hh
        dsimp only [D]
        nlinarith
      have hl := logPartition_lower_of_pointwise hn1 β
        (hH.continuous.comp (nestedLatitude_continuous w y r₀ t₀))
        (hH.continuous.comp (nestedLatitude_continuous w y r t)) hpoint
      have htlog : Real.log (1-t^2) ≤ 0 :=
        Real.log_nonpos (by nlinarith [(abs_lt.mp hta).1,(abs_lt.mp hta).2]) (by nlinarith [sq_nonneg t])
      have hexp : ((n+2:ℕ):ℝ)*Real.log (1-t^2) ≤ ((n-2:ℕ):ℝ)*Real.log (1-t^2) :=
        mul_le_mul_of_nonpos_right (by exact_mod_cast (show n-2 ≤ n+2 by omega)) htlog
      have htc := mul_le_mul_of_nonneg_left (htcost t ht) hN.le
      apply (mul_le_mul_iff_right₀ hM).mp
      rw [latitudePartitionProfile_mul,
        partitionAgainst_latitude_eq β hHr y t]
      have he : ((n+1:ℕ):ℝ)*(((n+2:ℕ):ℝ)/((n+1:ℕ):ℝ)*L)=((n+2:ℕ):ℝ)*L := by field_simp
      rw [he]
      change ((n+2:ℕ):ℝ)*L ≤ Real.log (partition n β (fun z => H (nestedLatitude w y r t z)))+
        ((n-2:ℕ):ℝ)*Real.log (1-t^2)/2
      dsimp only [D,Function.comp_def] at hl
      dsimp only [L]
      nlinarith
    have hi := hinner β Hr hHr y hy ((((n+2:ℕ):ℝ)/((n+1:ℕ):ℝ))*L) hinnerProf
    have hib := hi.trans (partitionOn_le_partition (by omega) β hHr (coreBand_measurable y t₀ wt))
    have hlog := Real.log_le_log (Real.exp_pos _) hib
    rw [Real.log_exp] at hlog
    have he : ((n+1:ℕ):ℝ)*((((n+2:ℕ):ℝ)/((n+1:ℕ):ℝ))*L-ε/4)=
        ((n+2:ℕ):ℝ)*L-((n+1:ℕ):ℝ)*ε/4 := by field_simp
    rw [he] at hlog
    have hlog' : L-ε/4 ≤ Real.log (partition (n+1) β Hr)/((n+2:ℕ):ℝ) := by
      apply (le_div_iff₀ hN).mpr
      have hdim : ((n+1:ℕ):ℝ) ≤ ((n+2:ℕ):ℝ) := by norm_num
      nlinarith
    have hp := latitudePartitionProfile_ge_entropy β H w hra
    rw [partitionAgainst_latitude_eq β hH.continuous w r] at hp
    have hrc := hrcost r hr
    dsimp only [L] at hlog'
    change Real.log (partition (n+1) β Hr)/((n+2:ℕ):ℝ)+Real.log (1-r^2)/2 ≤ _ at hp
    linarith
  have ho := houter β H hH.continuous w hw
    (B+(Real.log (1-r₀^2)+Real.log (1-t₀^2))/2-3*ε/4) hprof
  have hsub : coreBand w r₀ wr ⊆ overlapRegion w A := by
    rw [coreBand_eq_overlapRegion]
    exact fun x hx => hrsub hx
  have hmono : partitionOn β H (coreBand w r₀ wr) ≤ partitionOn β H (overlapRegion w A) := by
    exact integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (.of_forall (fun _ => (Real.exp_pos _).le))
      ((partition_integrand_integrable (by omega) β hH.continuous).restrict)
  convert ho.trans hmono using 1 <;> congr 1 <;> ring

end SlowEquilibration.SphericalNestedLatitude
