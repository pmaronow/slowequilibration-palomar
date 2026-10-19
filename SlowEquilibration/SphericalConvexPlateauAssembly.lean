-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauCommonEvent
public import SlowEquilibration.SphericalConvexMemory

@[expose] public section

/-! # Exact stronger-plateau assembly for the proved convex probability class

The sole additional input is convergence of the literal actual weighted
replica moment. The three conclusions retaining an exponential disorder
rate and the simultaneous probability-one event are stated separately.
This reduction does not assert the missing source moment convergence.
-/
namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalBarycenter SphericalQuantitativeTrap SphericalWeightedReplicaPlateau VaryingProbability
open SphericalLaplaceIdentification
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- The exact three source conclusions whose event keeps an exponential rate. -/
structure PersistentMemoryConclusions (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (D : Disorder N μ.maxDegree) (κ γ a c C : ℝ) : Prop where
  eigenvalue : (normalizedSphericalSpectralData hN β (fieldOfMixture μ D)
    (fieldOfMixture_contDiff μ D).continuous).eigenvalue (Nat.floor (Real.exp (κ*N))) ≤ Real.exp (-(2*γ)*N)
  typicalStartingPoints : ∃ X : Set (Vector N), MeasurableSet X ∧ X ⊆ {x | OnSphere x} ∧
    1-C*Real.exp (-a*N) ≤ (mixtureGibbsLaw μ β D).real X ∧
    ∀ x ∈ X, ∀ t ≤ memoryTime γ N,
      1-C*Real.exp (-a*N) ≤ totalVariation (mixedTransitionKernel μ D β t x) (mixtureGibbsLaw μ β D)
  stationaryInformation : ∀ t : ℝ≥0, 0 < t → t ≤ memoryTime γ N →
    ENNReal.ofReal (c*N) ≤ endpointMutualInformation (mixtureGibbsLaw μ β D)
      (mixedTransitionKernel μ D β t)

theorem MemoryConclusions.persistent {hN : 2 ≤ N} {μ : FiniteMixture} {β : ℝ}
    {D : Disorder N μ.maxDegree} {b κ γ γ' a c C : ℝ}
    (h : MemoryConclusions hN μ β D b κ γ a c C) (hγ : γ' ≤ γ) :
    PersistentMemoryConclusions hN μ β D κ γ' a c C := by
  have hTime : memoryTime γ' N ≤ memoryTime γ N := by
    change Real.exp (γ'*(N:ℝ)) ≤ Real.exp (γ*(N:ℝ))
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg N))
  refine ⟨h.eigenvalue.trans (Real.exp_le_exp.mpr ?_),?_,?_⟩
  · nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · obtain ⟨X,hXm,hXs,hMass,hTV⟩ := h.typicalStartingPoints
    exact ⟨X,hXm,hXs,hMass,fun x hx t ht => hTV x hx t (ht.trans hTime)⟩
  · intro t ht htTime
    exact h.stationaryInformation t ht (htTime.trans hTime)

private theorem decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.exp (-a*N)) atTop (𝓝 (0:ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply,neg_mul]

private theorem two_decay_eventually {r : ℝ} (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, 2*Real.exp (-r*N)≤Real.exp (-(r/2)*N) := by
  have ht : Tendsto (fun N : ℕ => 2*Real.exp (-(r/2)*N)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (decay (half_pos hr)).const_mul 2
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with N hN
  have hh := mul_le_mul_of_nonneg_right hN.le (Real.exp_pos (-(r/2)*N)).le
  rw [one_mul] at hh
  apply le_trans _ hh
  apply le_of_eq
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- All five exact source thm:main-plateau conclusions are assembled for
b<qStar, with the true convex probability estimates consumed internally.
The actual weighted-replica moment convergence is the remaining primitive
input; this theorem is therefore an assembly reduction, not a closed headline. -/
theorem convex_main_plateau_of_weightedReplicaMoment (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1:ℝ) 1) μ.xi) {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi)
    (hb : b ∈ Ioo (0:ℝ) (Thresholds.qStar μ.xi β))
    (hMoment : ∀ q₁ q₂ δ : ℝ, IsAdmissibleCollar μ β q₁ q₂ → 0 < δ →
      InProbability (fun N => disorderLaw N μ.maxDegree)
        (fun _N D => sourceWeightedReplicaMoment μ β D (plantedCoreCost μ β) δ q₁ q₂)
        (Thresholds.qStar μ.xi β)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      (∀ᶠ N : ℕ in atTop, ∃ Ω₀ : Set (Disorder N μ.maxDegree), MeasurableSet Ω₀ ∧
        (disorderLaw N μ.maxDegree).real Ω₀ᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ D ∈ Ω₀, ∀ hN : 2 ≤ N, PersistentMemoryConclusions hN μ β D κ γ a c C) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree),
        MeasurableSet Ω ∧ (disorderLaw N μ.maxDegree).real Ωᶜ < η ∧
        ∀ D ∈ Ω, ∀ hN : 2 ≤ N, MemoryConclusions hN μ β D b κ γ a c C) := by
  have hqStar := (μ.qStar_solves_plateau hβd).1
  let qStar := Thresholds.qStar μ.xi β
  have hqpos : 0 < qStar := hqStar.1
  let bP := (b+qStar)/2
  have hbP : 0 < bP := by dsimp [bP,qStar]; linarith [hb.1,hqStar.1]
  have hbPq : bP < qStar := by dsimp [bP,qStar]; linarith [hb.2]
  have hbbP : b < bP := by dsimp [bP,qStar]; linarith [hb.2]
  obtain ⟨q₁,q₂,hRoot,hc,hJ,hG,_hCap,_hCollar⟩ := exists_plantedTrial_certificate μ hβd hβs
    (show bP*qStar ∈ Ioo (0:ℝ) (qStar^2) from
      ⟨mul_pos hbP hqStar.1,by nlinarith [hqStar.1]⟩)
  have hq₁ : 0 < q₁ := hc.1
  have hq₁one : q₁ < 1 := (hc.2.1.trans hc.2.2.1).trans hqStar.2
  have hSquare : bP*qStar < q₁^2 := by
    have hs := Real.sq_sqrt (show 0≤bP*qStar from (mul_pos hbP hqpos).le)
    nlinarith [Real.sqrt_nonneg (bP*qStar)]
  let m := (q₁^2/bP+qStar)/2
  have hmTarget : qStar < m := by
    have hd := (lt_div_iff₀' hbP).mpr hSquare
    dsimp [m]
    linarith
  have hm : 0 < m := hqStar.1.trans hmTarget
  have hmSquare : bP*m < q₁^2 := by
    dsimp [m]
    field_simp
    nlinarith [hSquare]
  have hSqrtMargin : Real.sqrt bP*Real.sqrt m < q₁ := by
    have hs : (Real.sqrt bP*Real.sqrt m)^2=bP*m := by
      rw [mul_pow,Real.sq_sqrt hbP.le,Real.sq_sqrt hm.le]
    nlinarith [mul_nonneg (Real.sqrt_nonneg bP) (Real.sqrt_nonneg m)]
  let ε := min (((q₁-Real.sqrt bP*Real.sqrt m)/2)^2) (1/2)
  have hεpos : 0 < ε := lt_min (sq_pos_of_pos (by linarith)) (by norm_num)
  have hεone : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hMargin : Real.sqrt bP*Real.sqrt m+Real.sqrt ε < q₁ := by
    have hs := Real.sqrt_le_sqrt (min_le_left (((q₁-Real.sqrt bP*Real.sqrt m)/2)^2) (1/2))
    rw [Real.sqrt_sq (show 0≤(q₁-Real.sqrt bP*Real.sqrt m)/2 by linarith)] at hs
    linarith
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβd
  obtain ⟨R,hR,hRepBase⟩ := convex_replica_overlap_eventually μ hconv hβpos hβs ⟨hεpos,hεone⟩
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hRepBound : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ ≤ Real.exp (-R*N) := by
    filter_upwards [hRepBase,two_decay_eventually hR] with N hBase hAbsorb
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
  let δ := min (G/16) (J/16)
  let w := (qStar-q₂)/2
  have hδpos : 0 < δ := lt_min (by dsimp [G]; positivity) (by dsimp [J]; positivity)
  have hGap : 4*δ < G := by
    have hd := min_le_left (G/16) (J/16)
    dsimp [δ]
    change 0<G at hG
    linarith
  have hw : 0 < w := by dsimp [w,qStar]; linarith [hc.2.2.1]
  have hCore : q₂ ≤ qStar-w := by dsimp [w,qStar]; linarith [hc.2.2.1]
  obtain ⟨aG,haG,hGoodBound⟩ := convex_goodCapCoreCollarEvent_eventually μ hconv hβd hβs.le hc hδpos hw
  have hGood : Tendsto (fun N => (disorderLaw N μ.maxDegree).real
      (goodCapCoreCollarEvent (mixtureCoefficients μ) β (β^2*μ.xi 1/2) J G δ q₁ q₂ qStar w (Real.exp (-aG*N)))ᶜ)
      atTop (𝓝 (0:ℝ)) :=
    squeeze_zero' (.of_forall fun _ => measureReal_nonneg) hGoodBound
      (by simpa only [mul_zero] using (decay haG).const_mul 11)
  have hRep : Tendsto (fun N => (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ)
      atTop (𝓝 (0:ℝ)) :=
    squeeze_zero' (.of_forall fun _ => measureReal_nonneg) hRepBound (decay hR)
  have hUpgrade := plateauUpgradeEvent_failure_tendsto μ β (β^2*μ.xi 1/2) J G δ q₁ q₂ qStar w aG ε r m qStar
    hmTarget hGood hRep (hMoment q₁ q₂ δ hc hδpos)
  obtain ⟨cE,hcE,_hcEq,hBuild⟩ := constructed_plateau_upgrade_eventually J G δ q₁ q₂ aG ε bP b r m
    hJ hδpos.le hGap haG hq₁ hc.2.1 hεpos.le hbP.le hbbP hr hm hMargin
  obtain ⟨κ,γ₀,a,c,C,hκ,hγ₀,ha,hcM,hC,hBase⟩ := convex_main_memory μ hconv hβd hβs
    (show qStar^2/2 ∈ Ioo (0:ℝ) (qStar^2) from ⟨div_pos (sq_pos_of_pos hqpos) (by norm_num),by nlinarith [hqpos]⟩)
  let γ := min γ₀ (cE/4)
  have hγ : 0 < γ := lt_min hγ₀ (by positivity)
  have hγ₀le : γ ≤ γ₀ := min_le_left _ _
  have hγE : 2*γ < cE := by
    have hg := min_le_right γ₀ (cE/4)
    change γ≤cE/4 at hg
    linarith
  refine ⟨κ,γ,a,c,C,hκ,hγ,ha,hcM,hC,?_,?_⟩
  · filter_upwards [hBase] with N hBase
    obtain ⟨Ω,hΩ,hFail,hMem⟩ := hBase
    exact ⟨Ω,hΩ,hFail,fun D hD hN => (hMem D hD hN).persistent hγ₀le⟩
  · intro η hη
    have hBaseDecay : Tendsto (fun N : ℕ => C*Real.exp (-a*N)) atTop (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using (decay ha).const_mul C
    have hBaseSmall := hBaseDecay.eventually (gt_mem_nhds (half_pos hη))
    filter_upwards [hBase,hBuild γ hγ hγE,hUpgrade.eventually (gt_mem_nhds (half_pos hη)),hBaseSmall,eventually_ge_atTop 2]
      with N hBase hBuild hUpgrade hBaseSmall hDim
    obtain ⟨Ω₀,hΩ₀,hFail,hMem⟩ := hBase
    refine ⟨Ω₀∩plateauUpgradeEvent μ β (β^2*μ.xi 1/2) J G δ q₁ q₂ qStar w aG ε r m,?_,?_,?_⟩
    · exact hΩ₀.inter (plateauUpgradeEvent_measurable (show 1≤N by omega) μ β (β^2*μ.xi 1/2) J G δ q₁ q₂ qStar w aG ε r m)
    · rw [compl_inter]
      have hu := measureReal_union_le (μ := disorderLaw N μ.maxDegree) Ω₀ᶜ
        (plateauUpgradeEvent μ β (β^2*μ.xi 1/2) J G δ q₁ q₂ qStar w aG ε r m)ᶜ
      linarith
    · intro D hD hN
      obtain ⟨hProjection,hCorrelation⟩ := hBuild hN μ β (β^2*μ.xi 1/2) qStar w D hCore hD.2
      exact (hMem D hD.1 hN).replace_plateau hγ₀le (hbbP.le.trans hProjection) hCorrelation

end
end SlowEquilibration.SphericalMemoryAssembly
