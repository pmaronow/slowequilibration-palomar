-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeLatitudeMass
public import SlowEquilibration.SphericalPlateauAmplitudeDenominatorLower
public import SlowEquilibration.SphericalPlateauAmplitudeAwayPartitionUpper

@[expose] public section

/-! # Genuine all-finite weighted latitude localization in the actual bank -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter
open scoped Topology ENNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_amplitudeLatitudeBadMass_tail (μ : FiniteMixture)
    {β δ q₁ q₂ d : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (hd : 0<d) :
    ∃ η : ℝ,0<η ∧ ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
        (bankLaw n μ).real {D | Real.exp (-η*((n+1:ℕ):ℝ)) ≤
          amplitudeLatitudeBadMass μ β (plantedCoreCost μ β) δ q₁ q₂ (Thresholds.qStar μ.xi β) d
            x (latitudeFrameAt x) p₀ (fun _ => 1) D} ≤8*Real.exp (-γ*((n+1:ℕ):ℝ)) := by
  obtain ⟨a,ha,r,hr,hNum⟩ := exists_amplitudeRestrictedPartition_away_upper μ hβ hβs hc hδ p₀ hd
  obtain ⟨s,hs,hDen⟩ := general_amplitudePartition_closed_lower_tail μ (δ := δ) hβ hc (half_pos ha) p₀
  refine ⟨a/4,by positivity,min r s,lt_min hr hs,?_⟩
  filter_upwards [hNum,hDen] with n hNumN hDenN
  intro x hx
  let q := Thresholds.qStar μ.xi β
  let L := β^2*μ.xi 1/2-plantedCoreCost μ β
  let E := amplitudeLatitudeBadRegion x q d
  have hE : MeasurableSet E := amplitudeLatitudeBadRegion_measurable x q d
  have hEq : E=overlapRegion x {t : ℝ | d≤|t-q|} := by
    ext u
    change (d≤|overlap x u-q|)↔(d≤|overlap u x-q|)
    rw [show overlap x u=overlap u x by unfold overlap;rw [real_inner_comm]]
  let Z := fun D : BankDisorder n μ => amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂
    x (latitudeFrameAt x) p₀ (fun _ => 1) D
  let Zr := fun D : BankDisorder n μ => amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂
    x p₀ (fun _ => 1) E D
  let A : Set (BankDisorder n μ) := {D | Real.exp (((n+1:ℕ):ℝ)*(L-a))≤Zr D}
  let B : Set (BankDisorder n μ) := {D | Z D≤Real.exp (((n+1:ℕ):ℝ)*(L-a/2))}
  have hSub : {D | Real.exp (-(a/4)*((n+1:ℕ):ℝ))≤
      amplitudeLatitudeBadMass μ β (plantedCoreCost μ β) δ q₁ q₂ q d x (latitudeFrameAt x) p₀ (fun _ => 1) D}⊆A∪B := by
    intro D hD
    by_contra hBad
    have hNotA : D∉A := fun h => hBad (Or.inl h)
    have hNotB : D∉B := fun h => hBad (Or.inr h)
    have hNr : Zr D<Real.exp (((n+1:ℕ):ℝ)*(L-a)) := not_le.mp hNotA
    have hFull : Real.exp (((n+1:ℕ):ℝ)*(L-a/2))<Z D := not_le.mp hNotB
    have hPos : 0<Z D := amplitudePartition_pos μ β (plantedCoreCost μ β) δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D
    have hMul := mul_lt_mul_of_pos_left hFull (Real.exp_pos (-(a/2)*((n+1:ℕ):ℝ)))
    rw [← Real.exp_add] at hMul
    have hExp : -(a/2)*((n+1:ℕ):ℝ)+((n+1:ℕ):ℝ)*(L-a/2)=((n+1:ℕ):ℝ)*(L-a) := by ring
    rw [hExp] at hMul
    have hRatio : Zr D/Z D<Real.exp (-(a/2)*((n+1:ℕ):ℝ)) :=
      (div_lt_iff₀ hPos).mpr (hNr.trans hMul)
    have hMass : amplitudeLatitudeBadMass μ β (plantedCoreCost μ β) δ q₁ q₂ q d
        x (latitudeFrameAt x) p₀ (fun _ => 1) D=Zr D/Z D :=
      amplitudeWeightedLaw_real_eq_partition_ratio μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1) E hE D
    change Real.exp (-(a/4)*((n+1:ℕ):ℝ))≤
      amplitudeLatitudeBadMass μ β (plantedCoreCost μ β) δ q₁ q₂ q d x (latitudeFrameAt x) p₀ (fun _ => 1) D at hD
    rw [hMass] at hD
    have hExpLt : Real.exp (-(a/2)*((n+1:ℕ):ℝ))<Real.exp (-(a/4)*((n+1:ℕ):ℝ)) := by
      apply Real.exp_lt_exp.mpr
      have hN : 0<((n+1:ℕ):ℝ) := by positivity
      nlinarith
    exact (not_lt_of_ge hD) (hRatio.trans hExpLt)
  have hNr : (bankLaw n μ).real A≤2*Real.exp (-r*((n+1:ℕ):ℝ)) := by
    change (bankLaw n μ).real {D | Real.exp (((n+1:ℕ):ℝ)*(L-a))≤
      amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1) E D}≤_
    rw [hEq]
    exact hNumN x hx
  have hDr : (bankLaw n μ).real B≤6*Real.exp (-s*((n+1:ℕ):ℝ)) := by
    have ht := ENNReal.toReal_mono (by finiteness) (hDenN x hx)
    simpa only [B,Z,L,Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ht
  have hh := (measureReal_mono (μ := bankLaw n μ) hSub).trans (measureReal_union_le A B)
  have hN : 0≤((n+1:ℕ):ℝ) := by positivity
  have hR : Real.exp (-r*((n+1:ℕ):ℝ))≤Real.exp (-(min r s)*((n+1:ℕ):ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left r s])
  have hS : Real.exp (-s*((n+1:ℕ):ℝ))≤Real.exp (-(min r s)*((n+1:ℕ):ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right r s])
  change (bankLaw n μ).real {D | Real.exp (-(a/4)*((n+1:ℕ):ℝ))≤
    amplitudeLatitudeBadMass μ β (plantedCoreCost μ β) δ q₁ q₂ q d
      x (latitudeFrameAt x) p₀ (fun _ => 1) D}≤8*Real.exp (-(min r s)*((n+1:ℕ):ℝ))
  linarith

private theorem localization_decay {a : ℝ} (ha : 0<a) :
    Tendsto (fun n : ℕ => Real.exp (-a*((n+1:ℕ):ℝ))) atTop (𝓝 (0:ℝ)) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop ha)
  simpa only [Function.comp_def,neg_mul] using hh

/-- Genuine actual weighted latitude L¹ localization, uniformly over all
spherical references before choosing any dimension-dependent axis. -/
theorem general_amplitudeLatitudeL1_eventually_le (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
        amplitudeLatitudeL1 μ β (plantedCoreCost μ β) δ q₁ q₂ (Thresholds.qStar μ.xi β)
          x (latitudeFrameAt x) p₀ (fun _ => 1)≤ε := by
  intro ε hε
  obtain ⟨η,hη,γ,hγ,hTail⟩ := general_amplitudeLatitudeBadMass_tail μ (d := ε/2) hβ hβs hc hδ p₀ (half_pos hε)
  have hq := (μ.qStar_solves_plateau hβ).1
  have hDecay : Tendsto (fun n : ℕ => 2*Real.exp (-η*((n+1:ℕ):ℝ))+16*Real.exp (-γ*((n+1:ℕ):ℝ)))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,add_zero] using ((localization_decay hη).const_mul 2).add
      ((localization_decay hγ).const_mul 16)
  filter_upwards [hTail,hDecay.eventually (gt_mem_nhds (half_pos hε))] with n hTailN hSmall
  intro x hx
  have hh := amplitudeLatitudeL1_le_badMassTail μ β (plantedCoreCost μ β) δ q₁ q₂
    (show Thresholds.qStar μ.xi β∈Icc (0:ℝ) 1 from ⟨hq.1.le,hq.2.le⟩)
    (half_pos hε).le (Real.exp_nonneg (-η*((n+1:ℕ):ℝ))) x hx (latitudeFrameAt x) p₀ (fun _ => 1)
  have ht := hTailN x hx
  linarith

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
