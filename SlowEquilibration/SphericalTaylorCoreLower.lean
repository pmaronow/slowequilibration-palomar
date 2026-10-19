-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorGoodPlantedBand
public import SlowEquilibration.SphericalTaylorBandThickening
public import SlowEquilibration.SphericalPlantedConditionalBound
public import SlowEquilibration.SphericalOverlapPartitionMeasurable

@[expose] public section

/-! Genuine planted core partition lower bounds from the actual selected
critical thermal band and two successive exact spherical coarea formulas. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory Set Filter Classical Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem partitionOn_mono {N : ℕ} (hN : 1≤N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) {A B : Set (Vector N)} (hAB : A⊆B) :
    partitionOn β H A≤partitionOn β H B :=
  setIntegral_mono_set (partition_integrand_integrable hN β hH).restrict
    (.of_forall fun _ => (Real.exp_pos _).le) (.of_forall hAB)

theorem qStar_shifted_core_partition_lower_tail (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree)
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      disorderLaw (n+3) μ.maxDegree
        {J | partitionOn β (fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β w))
          (coreBand w Q δ)<Real.exp (((n+3 : ℕ) : ℝ)*(plantedProfileTrial μ β Q-ε))}≤
        6*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  have hQ : Q∈Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  obtain ⟨q,hq,hclose,η,hη,hgood⟩ := qStar_good_planted_transverse_band μ hscope hβ hδ (half_pos hε)
  have hqpos : 0<q := (Real.sqrt_pos.mpr hQ.1).trans hq.1
  have hqabs : |q|<1 := by rw [abs_of_pos hqpos]; exact hq.2
  obtain ⟨K,hK,hgrad⟩ := exists_planted_regularDisorder_gradient_bound μ β
  let A := Ioo (Q-δ) (Q+δ)
  have hrA : bandOuterLatitude Q q∈A := by
    have hh := abs_lt.mp hclose
    exact ⟨by linarith,by linarith⟩
  have hthick := transverseBand_partitionOn_eventually_lower_of_gradient_bound
    (β := β) hQ hqabs hK.le (half_pos hε) isOpen_Ioo hrA
  refine ⟨η,hη,?_⟩
  filter_upwards [hgood,(tendsto_add_atTop_nat 1).eventually hthick] with n hn hthick
  intro w hw
  let e := latitudeFrameAt w
  have he : ∀ z,inner ℝ (e z) w=0 := latitudeFrameAt_orthogonal w hw
  apply (measure_mono ?_).trans (hn w hw e he)
  intro J hJ hg
  obtain ⟨hreg,y,hy,hband⟩ := hg
  let H := fieldOfMixture μ (J+plantedShift (mixtureCoefficients μ) β w)
  have hH : Differentiable ℝ H :=
    (field_contDiff (mixtureCoefficients μ) _).differentiable (by simp)
  have hgH : ∀ x∈closedBall 0 (Real.sqrt ((n+3 : ℕ) : ℝ)),‖fderiv ℝ H x‖≤K*Real.sqrt ((n+3 : ℕ) : ℝ) := by
    intro x hx
    exact hgrad (n+3) (by omega) w hw J hreg x
      (by simpa only [mem_closedBall,dist_zero_right] using hx)
  let B := plantedProfileTrial μ β Q-ε/2-Real.log (1-Q)/2
  have hB : B≤transverseBandPressure μ w e q Q β (J+plantedShift (mixtureCoefficients μ) β w) y := by
    dsimp only [B]
    linarith
  have hz := hthick H hH hgH w hw y hy B hB
  have hexp : B+Real.log (1-Q)/2-ε/2=plantedProfileTrial μ β Q-ε := by dsimp only [B]; ring
  rw [hexp] at hz
  have hsub : overlapRegion w A⊆coreBand w Q δ := by
    intro x hx
    change overlap x w∈Ioo (Q-δ) (Q+δ) at hx
    change |overlap x w-Q|≤δ
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  exact (not_lt_of_ge (hz.trans (partitionOn_mono (by omega) β H hH.continuous hsub))) hJ

def coreLowerBadEvent (N : ℕ) (μ : FiniteMixture) (β δ ε : ℝ) :
    Set (Disorder N μ.maxDegree × Vector N) :=
  {z | partitionOn β (fieldOfMixture μ z.1) (coreBand z.2 (Thresholds.qStar μ.xi β) δ)<
    Real.exp ((N : ℝ)*(plantedProfileTrial μ β (Thresholds.qStar μ.xi β)-ε))}

theorem coreLowerBadEvent_measurable (N : ℕ) (μ : FiniteMixture) (β δ ε : ℝ) :
    MeasurableSet (coreLowerBadEvent N μ β δ ε) := by
  have hm := overlapRestrictedPartition_measurable (N := N) (mixtureCoefficients μ) β
    (A := Icc (Thresholds.qStar μ.xi β-δ) (Thresholds.qStar μ.xi β+δ)) measurableSet_Icc
  convert measurableSet_lt hm (measurable_const (a := Real.exp ((N : ℝ)*
    (plantedProfileTrial μ β (Thresholds.qStar μ.xi β)-ε)))) using 1
  ext z
  change (partitionOn β (fieldOfMixture μ z.1) (coreBand z.2 (Thresholds.qStar μ.xi β) δ)<_)↔_
  rw [coreBand_eq_overlapRegion]
  rfl

/-- The actual joint planted core lower bound. Its exponential probability
is derived without a free-energy lower or good-core premise. -/
theorem qStar_planted_core_partition_lower_tail (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree)
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      plantedLaw (N := n+3) (mixtureCoefficients μ) β (coreLowerBadEvent (n+3) μ β δ ε)≤
        ENNReal.ofReal (Real.exp (-γ*((n+3 : ℕ) : ℝ))) := by
  obtain ⟨η,hη,hbound⟩ := qStar_shifted_core_partition_lower_tail μ hscope hβ hδ hε
  have hdim : ∀ᶠ n : ℕ in atTop,polynomialAbsorptionThreshold 6 0 (η/2)≤((n+3 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (polynomialAbsorptionThreshold 6 0 (η/2)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast
      (show Nat.ceil (polynomialAbsorptionThreshold 6 0 (η/2))≤n+3 by omega))
  refine ⟨η/2,by positivity,?_⟩
  filter_upwards [hbound,hdim] with n hn hdim
  apply planted_measure_le_of_uniform_shift_probability (by omega) (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β (coreLowerBadEvent_measurable _ μ β δ ε) (Real.exp_pos _).le
  intro w hw
  apply (hn w hw).trans
  have hp := polynomial_le_exp_of_threshold 0 (by norm_num : (0 : ℝ)≤6) (half_pos hη) hdim
  simp only [pow_zero,mul_one] at hp
  calc
    _ = ENNReal.ofReal (6*Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ ENNReal.ofReal (Real.exp ((η/2)*((n+3 : ℕ) : ℝ))*Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 2; ring


/-- The same actual joint lower-tail theorem indexed by the literal ambient
size, with the codimension-three bookkeeping removed. -/
theorem qStar_planted_core_partition_lower_tail_allDimensions (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree)
    {β δ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ N : ℕ in atTop,
      plantedLaw (N := N) (mixtureCoefficients μ) β (coreLowerBadEvent N μ β δ ε)≤
        ENNReal.ofReal (Real.exp (-γ*(N : ℝ))) := by
  obtain ⟨γ,hγ,hbound⟩ := qStar_planted_core_partition_lower_tail μ hscope hβ hδ hε
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hbound
  refine ⟨γ,hγ,eventually_atTop.2 ⟨n₀+3,?_⟩⟩
  intro N hN
  obtain ⟨m,rfl⟩ : ∃ m : ℕ,N=m+3 := ⟨N-3,by omega⟩
  exact hn₀ m (by omega)

end
end SlowEquilibration.SphericalTaylorRemainder
