-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMemoryCommonEvent
public import SlowEquilibration.SphericalConvexGoodReferences
public import SlowEquilibration.SphericalConvexReplicaBound

@[expose] public section

/-! # Unconditional five-conclusion memory for globally convex finite mixtures

The threshold collar certificate, the true joint planted core and partition
upper tails, the proved replica-symmetric likelihood transfer, and actual
replica concentration are consumed internally. This is a proved covariance
class specialization of source thm:main-memory. It does not assert the
remaining general nonconvex odd-mixture stochastic estimates.
-/

namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalBarycenter SphericalQuantitativeTrap
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem absorb_two_eventually {r : ℝ} (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, 2*Real.exp (-r*N)≤Real.exp (-(r/2)*N) := by
  have ht : Tendsto (fun N : ℕ => 2*Real.exp (-(r/2)*N)) atTop (𝓝 (0 : ℝ)) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hr))
    simpa only [Function.comp_apply,neg_mul,mul_zero] using he.const_mul 2
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ)<1 by norm_num))] with N hN
  have hh := mul_le_mul_of_nonneg_right hN.le (Real.exp_pos (-(r/2)*N)).le
  rw [one_mul] at hh
  apply le_trans _ hh
  apply le_of_eq
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- Exact source thm:main-memory for globally convex finite covariances,
on one actual Borel disorder event with an exponential failure bound.
All scalar and quantitative probabilistic inputs are proved internally. -/
theorem convex_main_memory (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) ((Thresholds.qStar μ.xi β)^2)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ D ∈ Ω, ∀ hN : 2 ≤ N, MemoryConclusions hN μ β D b κ γ a c C := by
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβd
  obtain ⟨q₁,q₂,hbq,hc,hJ,hG,_hCapTrial,_hCollarTrial⟩ :=
    exists_plantedTrial_certificate μ hβd hβs hb
  have hqStar := (μ.qStar_solves_plateau hβd).1
  have hq₁ : q₁ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hc.1,(hc.2.1.trans hc.2.2.1).trans hqStar.2⟩
  let ε := min (((q₁-Real.sqrt b)/2)^2) ((q₁/4)^2/2)
  have hεpos : 0 < ε := lt_min (sq_pos_of_pos (by linarith))
    (div_pos (sq_pos_of_pos (by linarith [hq₁.1])) (by norm_num))
  have hεcap : ε≤(q₁/4)^2/2 := min_le_right _ _
  have hεone : ε<1 := by
    have hqpos := hq₁.1
    have hqone := hq₁.2
    nlinarith [sq_nonneg (1-q₁/4)]
  have hMargin : Real.sqrt b+Real.sqrt ε<q₁ := by
    have hh : ε≤((q₁-Real.sqrt b)/2)^2 := min_le_left _ _
    have hsqrt := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_sq (show 0≤(q₁-Real.sqrt b)/2 by linarith)] at hsqrt
    linarith
  obtain ⟨R,hR,hReplicaBase⟩ := convex_replica_overlap_eventually μ hconv hβpos hβs
    (show ε∈Ioo (0 : ℝ) 1 from ⟨hεpos,hεone⟩)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hReplica : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ ≤ Real.exp (-R*N) := by
    filter_upwards [hReplicaBase,absorb_two_eventually hR] with N hBase hAbsorb
    obtain ⟨Ω,_hΩ,hFail,hRep⟩ := hBase
    have hSubset : Ω ⊆ replicaTailEvent μ β ε r := by
      intro D hD
      let _ : IsProbabilityMeasure (mixtureGibbsLaw μ β D) :=
        gibbsLaw_probability_all N β (fieldOfMixture_contDiff μ D).continuous
      apply (measureReal_mono (show replicaOverlapEvent ε ⊆ absoluteReplicaOverlapEvent ε from
        fun z hz => by
          change ε<overlap z.1 z.2 at hz
          change ε≤|overlap z.1 z.2|
          exact hz.le.trans (le_abs_self _))).trans
      exact (hRep D hD).trans hAbsorb
    exact (measureReal_mono (compl_subset_compl.mpr hSubset)).trans hFail
  let J := plantedCoreCost μ β
  let G := plantedCollarGap μ β q₂
  let δ := min (G/16) (r/32)
  let w := (Thresholds.qStar μ.xi β-q₂)/2
  have hδpos : 0 < δ := lt_min (by dsimp [G]; positivity) (by positivity)
  have hGap : 4*δ<G := by
    have hh : δ≤G/16 := min_le_left _ _
    change 0<G at hG
    linarith
  have hδr : 4*δ<r/4 := by
    have hh : δ≤r/32 := min_le_right _ _
    linarith
  have hw : 0 < w := by dsimp [w]; linarith [hc.2.2.1]
  have hCore : q₂≤Thresholds.qStar μ.xi β-w := by dsimp [w]; linarith [hc.2.2.1]
  obtain ⟨a,ha,hGood⟩ := convex_goodCapCoreCollarEvent_eventually μ hconv hβd hβs.le hc hδpos hw
  apply constructed_memory_common_event_of_failure_bounds μ β (β^2*μ.xi 1/2) J G δ q₁ q₂
    (Thresholds.qStar μ.xi β) w a ε b r hJ hδpos.le hGap ha hq₁ hc.2.1 hCore
    hεpos.le hb.1.le hr hMargin hεcap hδr 11 1 a R
    (by norm_num) (by norm_num) ha hR hGood
  simpa only [one_mul] using hReplica

end
end SlowEquilibration.SphericalMemoryAssembly
