-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexReplicaTypicality
public import SlowEquilibration.SphericalReplicaFromTypical

@[expose] public section

/-! Actual exponentially small replica overlap and simultaneous cap mass
bounds for finite mixtures with covariance convex on [-1,1] below the static threshold. -/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual two-replica Gibbs law has exponentially small mass at every
fixed absolute overlap, outside an exponentially rare Borel disorder event. -/
theorem convex_replica_overlap_eventually (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ Real.exp (-c*(N : ℝ)) ∧
        ∀ J ∈ Ω, ((gibbsLaw N β (fieldOfMixture μ J)).prod
          (gibbsLaw N β (fieldOfMixture μ J))).real (absoluteReplicaOverlapEvent δ) ≤
            2*Real.exp (-c*(N : ℝ)) := by
  obtain ⟨c,hc,hev⟩ := convex_replica_typicality μ hconv hβ hβs hδ
  refine ⟨c,hc,?_⟩
  rw [← map_add_atTop_eq_nat 1]
  change ∀ᶠ n : ℕ in atTop, ∃ Ω : Set (Disorder (n+1) μ.maxDegree), _
  filter_upwards [hev] with n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hn
  refine ⟨Ω,hΩ,hfail,?_⟩
  intro J hJ
  obtain ⟨T,hT,_hTs,hbad,hsections⟩ := hgood J hJ
  let : IsProbabilityMeasure (gibbsLaw (n+1) β (fieldOfMixture μ J)) :=
    gibbsLaw_probability (by omega) β (fieldOfMixture_contDiff μ J).continuous
  have h := replica_mass_le_of_typical (gibbsLaw (n+1) β (fieldOfMixture μ J)) hT
    (Real.exp_pos _).le hbad hsections
  linarith

/-- Every cap of a fixed positive latitude has exponentially small Gibbs
mass on the same event, simultaneously for every physical axis. The axis
may therefore depend on the disorder. -/
theorem convex_uniform_cap_mass_eventually (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β s : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ Real.exp (-c*(N : ℝ)) ∧
        ∀ J ∈ Ω, ∀ v : Vector N, ‖v‖^2=(N : ℝ) →
          (gibbsLaw N β (fieldOfMixture μ J)).real (cap v s) ≤ Real.exp (-c*(N : ℝ)) := by
  have hδ : s^2/2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sq_pos_of_pos hs.1) (by norm_num)
    · nlinarith [hs.1,hs.2,sq_nonneg (1-s)]
  obtain ⟨r,hr,hrep⟩ := convex_replica_overlap_eventually μ hconv hβ hβs hδ
  let C : ℝ := (2-s^2)/s^2
  have hC : 0 ≤ C := by
    apply div_nonneg _ (sq_nonneg s)
    nlinarith [hs.1,hs.2,sq_nonneg (1-s)]
  refine ⟨r/4,by positivity,?_⟩
  rw [← map_add_atTop_eq_nat 1]
  change ∀ᶠ n : ℕ in atTop, ∃ Ω : Set (Disorder (n+1) μ.maxDegree), _
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hrep,
    weighted_exponential_eventually_le hr (2*C)] with n hrep htail
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hrep
  have hN : 1 ≤ n+1 := by omega
  have hNr : 0 ≤ ((n+1 : ℕ) : ℝ) := by positivity
  have he : Real.exp (-r*((n+1 : ℕ) : ℝ)) ≤ Real.exp (-(r/4)*((n+1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  refine ⟨Ω,hΩ,hfail.trans he,?_⟩
  intro J hJ v hv
  let ν := gibbsLaw (n+1) β (fieldOfMixture μ J)
  let : IsProbabilityMeasure ν := gibbsLaw_probability hN β (fieldOfMixture_contDiff μ J).continuous
  have hprod : (ν.prod ν).real (replicaOverlapEvent (s^2/2)) ≤ 2*Real.exp (-r*((n+1 : ℕ) : ℝ)) := by
    apply (measureReal_mono ?_).trans (hgood J hJ)
    intro z hz
    change s^2/2 < overlap z.1 z.2 at hz
    exact hz.le.trans (le_abs_self _)
  have hcap := cap_mass_sq_le_replica_mass hN ν (gibbsLaw_support hN β (fieldOfMixture μ J)) v hv hs
  have hbound : (ν.real (cap v s))^2 ≤ Real.exp (-(r/2)*((n+1 : ℕ) : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hprod hC
    change (ν.real (cap v s))^2 ≤ C*(ν.prod ν).real (replicaOverlapEvent (s^2/2)) at hcap
    calc
      _ ≤ C*(2*Real.exp (-r*((n+1 : ℕ) : ℝ))) := hcap.trans hm
      _ = (2*C)*Real.exp (-r*((n+1 : ℕ) : ℝ)) := by ring
      _ ≤ _ := htail
  have hsquare : (Real.exp (-(r/4)*((n+1 : ℕ) : ℝ)))^2 =
      Real.exp (-(r/2)*((n+1 : ℕ) : ℝ)) := by
    rw [sq,← Real.exp_add]
    congr 1
    ring
  rw [← hsquare] at hbound
  exact (sq_le_sq₀ measureReal_nonneg (Real.exp_pos _).le).mp hbound

end SlowEquilibration.SphericalModel
