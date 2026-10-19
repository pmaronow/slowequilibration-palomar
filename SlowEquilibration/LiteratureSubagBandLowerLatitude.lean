-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerProof

/-!
The samplewise latitude-slice comparison retains the full transverse
replica block and all real temperatures. The latitude entropy in Subag's
lower band argument is obtained from a positive radial interval on the
equator side of the prescribed latitude. Its exact finite-dimensional
prefactor is retained before taking the limit. The expectation comparison
and integration of the independent slice coordinates remain separate steps.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerLatitude

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof LiteratureSubagBandLowerProof
open LiteratureSubagTheorem10Proof
open SphericalGaussianJet PairConditionalDeterminantMoments SphericalTwoPointCovariance
open scoped Topology BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem replicatedBand_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem overlapBlock_measurable {N k : ℕ} (θ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) 0 θ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

/-- Independent latitude slices retain the central transverse block
partition, up to the extensive deterministic variation cost. This is the
samplewise comparison before integrating the latitude coordinates. -/
theorem regularDisorder_variableLatitude_partition_lower {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (μ : FiniteMixture) (β : ℝ)
    (J : Disorder (n + 1) μ.maxDegree) (hJ : J ∈ regularDisorder)
    {q δ ρ η θ : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hηδ : η ≤ δ) (hwidth : 2 * η + θ ≤ ρ)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ x, inner ℝ (e x) u = 0)
    (r : Fin k → ℝ) (hr : ∀ i, |r i| ≤ 1)
    (hnear : ∀ i, |r i - Real.sqrt q| ≤ η) :
    Real.exp (-(2 * |β| * derivativeConstant (mixtureCoefficients μ) * Real.sqrt η) *
        (((n + 1 : ℕ) : ℝ) * (k : ℝ))) *
      (∫ y in overlapBlock 0 θ,
        Real.exp (β * ∑ i : Fin k,
          (field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i)) -
            field (mixtureCoefficients μ) J (Real.sqrt q • u)))
        ∂Measure.pi (fun _ : Fin k => sphereLaw n)) ≤
      ∫ σ in ReplicatedBand k q δ ρ (Real.sqrt q • u),
        Real.exp (β * ∑ i : Fin k,
          (field (mixtureCoefficients μ) J (σ i) -
            field (mixtureCoefficients μ) J (Real.sqrt q • u)))
        ∂Measure.pi (fun i : Fin k => latitudeLaw u e (r i)) := by
  let T : (Fin k → Vector n) → Fin k → Vector (n + 1) :=
    fun y i => latitudeMap u e (r i) (y i)
  have hT : Measurable T := .of_eval (fun i =>
    (latitudeMap_continuous u e (r i)).measurable.comp (measurable_pi_apply i))
  let H := field (mixtureCoefficients μ) J
  let m := Real.sqrt q • u
  let F : (Fin k → Vector (n + 1)) → ℝ :=
    fun σ => Real.exp (β * ∑ i : Fin k, (H (σ i) - H m))
  let G : (Fin k → Vector n) → ℝ :=
    fun y => Real.exp (β * ∑ i : Fin k,
      (H (latitudeMap u e (Real.sqrt q) (y i)) - H m))
  let B := ReplicatedBand k q δ ρ m
  let A : Set (Fin k → Vector n) := overlapBlock 0 θ
  let E := 2 * |β| * derivativeConstant (mixtureCoefficients μ) * Real.sqrt η
  have hB : MeasurableSet B := replicatedBand_measurable q δ ρ m
  have hA : MeasurableSet A := overlapBlock_measurable θ
  have hF : Measurable F := by
    dsimp [F, H]
    exact (Real.continuous_exp.comp
      ((continuous_finsetSum _ (fun i _ =>
        ((field_contDiff _ J).continuous.comp (continuous_apply i)).sub
          continuous_const)).const_mul β)).measurable
  have hi (s : Fin k → ℝ) : Integrable
      (fun y : Fin k → Vector n => Real.exp (β * ∑ i : Fin k,
        (H (latitudeMap u e (s i) (y i)) - H m)))
      (Measure.pi (fun _ : Fin k => sphereLaw n)) := by
    have hsingle (i : Fin k) : Integrable
        (fun x : Vector n => Real.exp (β * (H (latitudeMap u e (s i) x) - H m)))
        (sphereLaw n) :=
      partition_integrand_integrable hn β
        (((field_contDiff _ J).continuous.comp (latitudeMap_continuous u e _)).sub
          continuous_const)
    convert Integrable.fintype_prod hsingle using 1
    ext y
    rw [Finset.mul_sum, Real.exp_sum]
  have hiG : Integrable G (Measure.pi (fun _ : Fin k => sphereLaw n)) := hi (fun _ => Real.sqrt q)
  have hiFT : Integrable (fun y => F (T y)) (Measure.pi (fun _ : Fin k => sphereLaw n)) := hi r
  have hmap : Measure.pi (fun i : Fin k => latitudeLaw u e (r i)) =
      (Measure.pi (fun _ : Fin k => sphereLaw n)).map T := by
    unfold latitudeLaw
    exact (Measure.pi_map_pi (fun i : Fin k =>
      (latitudeMap_continuous u e (r i)).measurable.aemeasurable)).symm
  change Real.exp (-E * (((n + 1 : ℕ) : ℝ) * (k : ℝ))) *
    (∫ y in A, G y ∂Measure.pi (fun _ : Fin k => sphereLaw n)) ≤
      ∫ σ in B, F σ ∂Measure.pi (fun i : Fin k => latitudeLaw u e (r i))
  rw [← integral_indicator hB, hmap, integral_map hT.aemeasurable
    (hF.indicator hB).aestronglyMeasurable, ← integral_indicator hA, ← integral_const_mul]
  have hcomp : (fun y => B.indicator F (T y)) = (T ⁻¹' B).indicator (fun y => F (T y)) := rfl
  rw [hcomp]
  apply integral_mono_ae ((hiG.indicator hA).const_mul _) (hiFT.indicator (hB.preimage hT))
  have hsupp : ∀ᵐ y ∂Measure.pi (fun _ : Fin k => sphereLaw n),
      ∀ i : Fin k, ‖y i‖ ^ 2 = (n : ℝ) :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin k => sphereLaw n) (i := i)).eventually (sphereLaw_support hn))
  filter_upwards [hsupp] with y hy
  by_cases hya : y ∈ A
  · have hmem : T y ∈ B :=
      LiteratureSubagBandLowerFinal.variableLatitude_mem_replicatedBand hn hq hηδ hwidth
        u hu e he r hr hnear y (by simpa [A, overlapBlock] using hya)
    rw [indicator_of_mem hya, indicator_of_mem (show y ∈ T ⁻¹' B from hmem)]
    dsimp only [G, F]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha : |Real.sqrt q| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg q)]
      exact Real.sqrt_le_one.mpr hq.2.le
    have hv := regularDisorder_replicatedLatitude_variation hn hk (mixtureCoefficients μ)
      β J hJ u hu e he ha r hr hnear y hy
    have hden : 0 < ((n + 1 : ℕ) : ℝ) * (k : ℝ) := by
      exact mul_pos (by positivity) (Nat.cast_pos.mpr (by omega))
    have hcost := (div_le_iff₀ hden).mp hv
    dsimp only [T, H, m, E]
    simp only [Finset.sum_sub_distrib] at hcost ⊢
    linarith [neg_le_abs (β *
      (∑ i : Fin k, field (mixtureCoefficients μ) J (latitudeMap u e (r i) (y i)) -
        ∑ i : Fin k, field (mixtureCoefficients μ) J (latitudeMap u e (Real.sqrt q) (y i))))]
  · rw [indicator_of_notMem hya, mul_zero]
    exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

/-- A radial interval on the equator side of a latitude has the exact
latitude entropy as a lower bound, with a positive dimension-free factor. -/
theorem latitude_slab_mass_lower
    {a η : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ u : Vector (n + 1), ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ) →
      C * Real.exp (((n - 2 : ℕ) : ℝ) / 2 * Real.log (1 - a ^ 2)) ≤
        (sphereLaw (n + 1)).real (overlapRegion u {r | |r - a| ≤ η}) := by
  let τ := min η (a / 2)
  let b := Real.sqrt (2 * (1 - a))
  let c := Real.sqrt (2 * (1 - a + τ))
  have hτ : 0 < τ := lt_min hη (div_pos ha.1 (by norm_num))
  have hτη : τ ≤ η := min_le_left _ _
  have hτa : τ ≤ a / 2 := min_le_right _ _
  have hb : 0 < b := by dsimp [b]; exact Real.sqrt_pos.mpr (by linarith [ha.2])
  have hb2 : b ^ 2 = 2 * (1 - a) := by
    dsimp [b]
    exact Real.sq_sqrt (by linarith [ha.2])
  have hc2 : c ^ 2 = 2 * (1 - a + τ) := by
    dsimp [c]
    exact Real.sq_sqrt (by linarith [ha.2])
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hbc : b < c := by nlinarith
  have hc : c < 2 := by nlinarith [ha.1]
  have harg : 0 < 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
  refine ⟨b * (c - b) / 4, by positivity, ?_⟩
  intro n hn u hu
  let A : Set ℝ := {r | |r - a| ≤ η}
  have hA : MeasurableSet A := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hrange (r : ℝ) (hr : r ∈ Icc b c) :
      a - τ ≤ radialLatitude r ∧ radialLatitude r ≤ a := by
    have hr0 : 0 < r := hb.trans_le hr.1
    dsimp [radialLatitude]
    constructor <;> nlinarith [sq_le_sq₀ hb.le hr0.le |>.mpr hr.1,
      sq_le_sq₀ hr0.le hc0 |>.mpr hr.2]
  have hband (r : ℝ) (hr : r ∈ Icc b c) : radialLatitude r ∈ A := by
    obtain ⟨hlo, hhi⟩ := hrange r hr
    change |radialLatitude r - a| ≤ η
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let M := ((n - 2 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) * Real.log (1 - a ^ 2)
  have hlower (r : ℝ) (hr : r ∈ Icc b c) :
      M ≤ latitudePartitionProfile n 0 (fun _ => 0) u (radialLatitude r) := by
    obtain ⟨hlo, hhi⟩ := hrange r hr
    have hr0 : 0 ≤ radialLatitude r := by linarith [ha.1]
    have hbase : 1 - a ^ 2 ≤ 1 - (radialLatitude r) ^ 2 := by nlinarith
    have hlog := Real.log_le_log harg hbase
    simpa only [latitudePartitionProfile, partitionAgainst, zero_mul, Real.exp_zero,
      integral_const, probReal_univ, one_smul, Real.log_one, zero_div, zero_add, M]
      using mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ ((n - 2 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) by positivity)
  have hpart := partitionOn_ge_latitudeProfile_lower hn (0 : ℝ) continuous_const u hu
    hA hb hbc.le hc hband hlower
  have hmass : partitionOn (0 : ℝ) (fun _ : Vector (n + 1) => 0) (overlapRegion u A) =
      (sphereLaw (n + 1)).real (overlapRegion u A) := by
    simp only [partitionOn, zero_mul, Real.exp_zero, integral_const,
      smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  have hexponent : ((n + 1 : ℕ) : ℝ) * M =
      ((n - 2 : ℕ) : ℝ) / 2 * Real.log (1 - a ^ 2) := by
    dsimp [M]
    field_simp
  rw [hmass, hexponent] at hpart
  calc
    _ ≤ (latitudeNormalization n).toReal * b * (c - b) *
        Real.exp (((n - 2 : ℕ) : ℝ) / 2 * Real.log (1 - a ^ 2)) := by
      have hnorm := latitudeNormalization_toReal_ge_quarter hn
      nlinarith [mul_le_mul_of_nonneg_right hnorm
        (show 0 ≤ b * (c - b) *
          Real.exp (((n - 2 : ℕ) : ℝ) / 2 * Real.log (1 - a ^ 2)) by positivity)]
    _ ≤ _ := hpart

/-- Every fixed positive window around an interior positive latitude has
at least the central latitude's entropy, uniformly over its axial center. -/
theorem latitude_slab_entropy_eventually_lower
    {a η ε : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n + 1),
      ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ) →
      Real.log (1 - a ^ 2) / 2 - ε ≤
        Real.log ((sphereLaw (n + 1)).real
          (overlapRegion u {r | |r - a| ≤ η})) / ((n + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := latitude_slab_mass_lower ha hη
  have herr : Tendsto (fun n : ℕ =>
      (Real.log C - 3 * Real.log (1 - a ^ 2) / 2) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log C - 3 * Real.log (1 - a ^ 2) / 2)).comp (tendsto_add_atTop_nat 1)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    herr.eventually (lt_mem_nhds (show -ε < (0 : ℝ) by linarith))] with n hn he
  intro u hu
  have hlower := hbound n hn u hu
  have hpositive : 0 < C * Real.exp
      (((n - 2 : ℕ) : ℝ) / 2 * Real.log (1 - a ^ 2)) := by positivity
  have hlog := Real.log_le_log hpositive hlower
  rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast] at hlog
  apply (le_div_iff₀ (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity)).mpr
  have he' := (lt_div_iff₀ (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity)).mp he
  push_cast at *
  nlinarith

/-- In the physical band coordinates, every fixed positive width has
the exact central entropy as an eventual lower bound. -/
theorem physical_band_entropy_eventually_lower
    {q η ε : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ u : Vector (n + 1),
      ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ) →
      Real.log (1 - q) / 2 - ε ≤
        Real.log ((sphereLaw (n + 1)).real
          {σ | |overlap σ (Real.sqrt q • u) - q| ≤ η * Real.sqrt q}) /
            ((n + 1 : ℕ) : ℝ) := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq.1
  have hs1 : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq.1.le, Real.sqrt_nonneg q, hq.2]
  filter_upwards [latitude_slab_entropy_eventually_lower ⟨hs, hs1⟩ hη hε]
    with n hn
  intro u hu
  have hset : {σ : Vector (n + 1) |
      |overlap σ (Real.sqrt q • u) - q| ≤ η * Real.sqrt q} =
      overlapRegion u {r | |r - Real.sqrt q| ≤ η} := by
    ext σ
    change |overlap σ (Real.sqrt q • u) - q| ≤ η * Real.sqrt q ↔
      |overlap σ u - Real.sqrt q| ≤ η
    have heq : overlap σ (Real.sqrt q • u) - q =
        Real.sqrt q * (overlap σ u - Real.sqrt q) := by
      unfold overlap
      rw [real_inner_smul_right, mul_sub, ← pow_two, Real.sq_sqrt hq.1.le]
      ring
    rw [heq, abs_mul, abs_of_pos hs, mul_comm η (Real.sqrt q)]
    exact mul_le_mul_iff_right₀ hs
  rw [hset]
  simpa only [Real.sq_sqrt hq.1.le] using hn u hu

end SlowEquilibration.LiteratureSubagBandLowerLatitude
