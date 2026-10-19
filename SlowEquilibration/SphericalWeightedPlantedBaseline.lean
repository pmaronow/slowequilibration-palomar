-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedSignedPartitionUpper
public import SlowEquilibration.SphericalSourceWeightedPartition
public import SlowEquilibration.PlantedCollarGeometry

@[expose] public section

/-! # Actual unperturbed weighted planted pressure

The genuine critical core lower tail and signed planted full/cap upper
tails imply the literal weighted pressure concentrates at F-J. All
probability estimates are derived internally in the stated convex scope.
-/
namespace SlowEquilibration.SphericalSourceWeightedPartition
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalTaylorRemainder
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal original Gaussian disorder pressure after the true planted
translation and the exact source overlap penalty. -/
def sourceWeightedPlantedPressure {N : ℕ} (μ : FiniteMixture) (β δ q₁ q₂ : ℝ)
    (x : Vector N) (D : Disorder N μ.maxDegree) : ℝ :=
  Real.log (sourceWeightedPartition β
    (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
    (plantedCoreCost μ β) δ q₁ q₂ x)/(N : ℝ)

/-- The actual weighted planted pressure has exponential closed tails at
the source value F-J, uniformly over every spherical reference point. -/
theorem convex_sourceWeightedPlantedPressure_closed_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ q₁ q₂ ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hδ : 0 ≤ δ)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (x : Vector N), ‖x‖^2=(N : ℝ) →
        disorderLaw N μ.maxDegree {D | ε ≤ |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-
          (β^2*μ.xi 1/2-plantedCoreCost μ β)|} ≤
            8*ENNReal.ofReal (Real.exp (-γ*(N : ℝ))) := by
  let F := β^2*μ.xi 1/2
  let J := plantedCoreCost μ β
  let Q := Thresholds.qStar μ.xi β
  let w := (Q-q₂)/2
  have hw : 0 < w := by dsimp only [w,Q]; linarith [hc.2.2.1]
  have hq₂ : q₂ < Q := hc.2.2.1
  have hcore : q₂ ≤ Q-w := by dsimp only [w]; linarith [hq₂]
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hJ : 0 ≤ J := by
    have hp := (μ.Phi_nonpos_iff_le_staticThreshold hβpos.le).mpr hβs
      Q (μ.qStar_solves_plateau hβ).1
    dsimp only [J,plantedCoreCost]
    linarith
  have hK : 0 ≤ sourceK J δ := by unfold sourceK; linarith
  obtain ⟨η,hη,hcoreTail⟩ := qStar_shifted_core_partition_lower_tail μ (Or.inl hconv)
    hβ hw (show 0 < ε/2 by positivity)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hcoreTail
  have hcoreAll : ∀ᶠ N : ℕ in atTop, ∀ (x : Vector N), ‖x‖^2=(N : ℝ) →
      disorderLaw N μ.maxDegree {D | partitionOn β
        (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
        (coreBand x Q w)<Real.exp ((N : ℝ)*(F-J-ε/2))} ≤
          6*ENNReal.ofReal (Real.exp (-η*(N : ℝ))) := by
    refine eventually_atTop.2 ⟨n₀+3,?_⟩
    intro N hN
    obtain ⟨n,rfl⟩ : ∃ n : ℕ,N=n+3 := ⟨N-3,by omega⟩
    intro x hx
    have ht := hn₀ n (by omega) x hx
    simpa only [Q,F,J,plantedProfileTrial_qStar_eq] using ht
  obtain ⟨γF,hγF,hFull⟩ := convex_shifted_full_partition_upper_tail μ hconv hβpos hβs
    (show 0 < ε/4 by positivity)
  obtain ⟨hcap,_hcollar⟩ := plantedProfileTrial_cap_collar_bounds μ hβ hc
  obtain ⟨γC,hγC,hCap⟩ := convex_shifted_signed_partition_upper_tail μ hconv hβpos
    (show 0 < ε/4 by positivity) (A := Ici q₁) measurableSet_Ici (M := F-J) (by
      intro r hr hr'
      rw [abs_of_nonneg (hc.1.le.trans hr)]
      exact hcap r ⟨hr,hr'.2⟩)
  let γ := min η (min γF γC)
  have hγ : 0 < γ := lt_min hη (lt_min hγF hγC)
  have hExp : Tendsto (fun N : ℕ => Real.exp ((ε/4)*(N : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity))
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hcoreAll,hFull,hCap,hExp.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with N hCoreN hFullN hCapN hTwo hN
  intro x hx
  let H := fun D : Disorder N μ.maxDegree =>
    fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)
  let E₀ : Set (Disorder N μ.maxDegree) := {D | partitionOn β (H D) (coreBand x Q w)<
    Real.exp ((N : ℝ)*(F-J-ε/2))}
  let E₁ : Set (Disorder N μ.maxDegree) := {D | Real.exp ((N : ℝ)*(F+ε/4))<partition N β (H D)}
  let E₂ : Set (Disorder N μ.maxDegree) := {D | Real.exp ((N : ℝ)*(F-J+ε/4))<
    partitionOn β (H D) (cap x q₁)}
  have hsub : {D | ε ≤ |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-(F-J)|} ⊆
      E₀ ∪ (E₁ ∪ E₂) := by
    intro D hD
    by_contra hbad
    have hnot₀ : D ∉ E₀ := fun h => hbad (Or.inl h)
    have hnot₁ : D ∉ E₁ := fun h => hbad (Or.inr (Or.inl h))
    have hnot₂ : D ∉ E₂ := fun h => hbad (Or.inr (Or.inr h))
    have hH : Continuous (H D) := (fieldOfMixture_contDiff μ _).continuous
    have hW : 0 < sourceWeightedPartition β (H D) J δ q₁ q₂ x :=
      sourceWeightedPartition_pos hN β hH J δ q₁ q₂ x
    have hLower : Real.exp ((N : ℝ)*(F-J-ε/2)) ≤
        sourceWeightedPartition β (H D) J δ q₁ q₂ x :=
      (le_of_not_gt hnot₀).trans (core_partition_le_sourceWeightedPartition hN β hH
        J δ q₁ q₂ Q w hc.2.1 hcore x)
    have hUpper₀ := sourceWeightedPartition_le_suppressed_full_add_cap hN β hH
      J δ q₁ q₂ hK hc.2.1 x
    have hFullBound : partition N β (H D) ≤ Real.exp ((N : ℝ)*(F+ε/4)) := le_of_not_gt hnot₁
    have hCapBound : partitionOn β (H D) (cap x q₁) ≤ Real.exp ((N : ℝ)*(F-J+ε/4)) :=
      le_of_not_gt hnot₂
    have hSuppressed : Real.exp (-2*(N : ℝ)*sourceK J δ)*partition N β (H D) ≤
        Real.exp ((N : ℝ)*(F-J+ε/4)) := by
      apply (mul_le_mul_of_nonneg_left hFullBound (Real.exp_pos _).le).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hgap := sourceK_gap J δ
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hSum : 2*Real.exp ((N : ℝ)*(F-J+ε/4)) ≤
        Real.exp ((N : ℝ)*(F-J+ε/2)) := by
      calc
        _ ≤ Real.exp ((ε/4)*(N : ℝ))*Real.exp ((N : ℝ)*(F-J+ε/4)) :=
          mul_le_mul_of_nonneg_right hTwo (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hUpper : sourceWeightedPartition β (H D) J δ q₁ q₂ x ≤
        Real.exp ((N : ℝ)*(F-J+ε/2)) :=
      hUpper₀.trans ((by linarith : Real.exp (-2*(N : ℝ)*sourceK J δ)*partition N β (H D)+
        partitionOn β (H D) (cap x q₁) ≤ 2*Real.exp ((N : ℝ)*(F-J+ε/4))).trans hSum)
    have hlo : (N : ℝ)*(F-J-ε/2) ≤ Real.log (sourceWeightedPartition β (H D) J δ q₁ q₂ x) := by
      exact Real.exp_le_exp.mp (by simpa only [Real.exp_log hW] using hLower)
    have hhi : Real.log (sourceWeightedPartition β (H D) J δ q₁ q₂ x) ≤ (N : ℝ)*(F-J+ε/2) := by
      exact Real.exp_le_exp.mp (by simpa only [Real.exp_log hW] using hUpper)
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hpLo : F-J-ε/2 ≤ sourceWeightedPlantedPressure μ β δ q₁ q₂ x D := by
      apply (le_div_iff₀ hNr).mpr
      change (F-J-ε/2)*(N : ℝ) ≤ _
      simpa only [mul_comm] using hlo
    have hpHi : sourceWeightedPlantedPressure μ β δ q₁ q₂ x D ≤ F-J+ε/2 := by
      apply (div_le_iff₀ hNr).mpr
      change _ ≤ (F-J+ε/2)*(N : ℝ)
      simpa only [mul_comm] using hhi
    have hpAbs : |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-(F-J)| ≤ ε/2 :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    change ε ≤ |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-(F-J)| at hD
    linarith
  have hc₀ : disorderLaw N μ.maxDegree E₀ ≤ 6*ENNReal.ofReal (Real.exp (-η*(N : ℝ))) := hCoreN x hx
  have hc₁ : disorderLaw N μ.maxDegree E₁ ≤ ENNReal.ofReal (Real.exp (-γF*(N : ℝ))) := hFullN x hx
  have hc₂ : disorderLaw N μ.maxDegree E₂ ≤ ENNReal.ofReal (Real.exp (-γC*(N : ℝ))) := by
    change disorderLaw N μ.maxDegree {D | Real.exp ((N : ℝ)*(F-J+ε/4))<
      partitionOn β (field (mixtureCoefficients μ) (D+plantedShift (mixtureCoefficients μ) β x))
        {u | q₁ ≤ overlap u x}} ≤ _
    simpa only [overlapRestrictedPartition,mem_Ici] using hCapN x hx
  have he (r : ℝ) (hr : γ ≤ r) : ENNReal.ofReal (Real.exp (-r*(N : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-γ*(N : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hr) (Nat.cast_nonneg N)
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add hc₀ ((measure_union_le _ _).trans (add_le_add hc₁ hc₂))).trans
  have he₀ := he η (min_le_left _ _)
  have he₁ := he γF ((min_le_right _ _).trans (min_le_left _ _))
  have he₂ := he γC ((min_le_right _ _).trans (min_le_right _ _))
  calc
    _ ≤ 6*ENNReal.ofReal (Real.exp (-γ*(N : ℝ)))+
        (ENNReal.ofReal (Real.exp (-γ*(N : ℝ)))+ENNReal.ofReal (Real.exp (-γ*(N : ℝ)))) :=
      add_le_add (mul_le_mul' le_rfl he₀) (add_le_add he₁ he₂)
    _ = _ := by ring

end
end SlowEquilibration.SphericalSourceWeightedPartition
