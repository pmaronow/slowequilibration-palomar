-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSourceObservablePlateau
public import SlowEquilibration.SphericalCapFrameModes
public import SlowEquilibration.SphericalQuantitativeTrap

@[expose] public section

/-! # Five literal memory conclusions from actual cap/core/collar and replica events

Every spectral object and every diffusion law below is the constructed
physical spherical model. The overlap-weighted observable is constructed
internally from its actual restricted-partition tests. A single replica
event also supplies all-axis cap bounds; no slow-mode, correlation,
trapping or information conclusion is used as an input.
-/

namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalPhysicalSpectral SphericalLaplaceIdentification
open SphericalBarycenter SphericalCenteredObservables SphericalSpinProjection
open SphericalSpinCorrelation SphericalQuantitativeTrap SphericalSourceObservablePlateau
open SphericalCapFrameCount SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- The five exact finite-volume conclusions of source thm:main-memory.
The spectral cutoff is positive, the spin is centered and normalized,
and all dynamic quantities use the actual stationary physical process. -/
structure MemoryConclusions (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (D : Disorder N μ.maxDegree) (b κ γ a c C : ℝ) : Prop where
  eigenvalue : (normalizedSphericalSpectralData hN β (fieldOfMixture μ D)
    (fieldOfMixture_contDiff μ D).continuous).eigenvalue (Nat.floor (Real.exp (κ*N))) ≤ Real.exp (-(2*γ)*N)
  spinProjection : b ≤ ‖vectorCutoff hN μ D β (Real.exp (-(2*γ)*N))
    (centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp)))‖^2
  connectedCorrelation : ∀ t ≤ memoryTime γ N, b ≤ connectedSpinCorrelation μ D β t
  typicalStartingPoints : ∃ X : Set (Vector N), MeasurableSet X ∧ X ⊆ {x | OnSphere x} ∧
    1-C*Real.exp (-a*N) ≤ (mixtureGibbsLaw μ β D).real X ∧
    ∀ x ∈ X, ∀ t ≤ memoryTime γ N,
      1-C*Real.exp (-a*N) ≤ totalVariation (mixedTransitionKernel μ D β t x) (mixtureGibbsLaw μ β D)
  stationaryInformation : ∀ t : ℝ≥0, 0 < t → t ≤ memoryTime γ N →
    ENNReal.ofReal (c*N) ≤ endpointMutualInformation (mixtureGibbsLaw μ β D)
      (mixedTransitionKernel μ D β t)

private lemma exp_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.exp (-a*N)) atTop (𝓝 (0 : ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply,neg_mul]

/-- The same replica tail used for magnetization supplies the genuine cap
mass bound simultaneously in every physical direction. -/
theorem uniform_caps_of_replica_eventually {s ε r : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hε : ε ≤ s^2/2) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ (_hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
      (D : Disorder N μ.maxDegree),
      ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real (replicaOverlapEvent ε) ≤
        Real.exp (-r*N) →
      ∀ v : Vector N, OnSphere v →
        (mixtureGibbsLaw μ β D).real (cap v s) ≤ Real.exp (-(r/4)*N) := by
  let K := (2-s^2)/s^2
  have hK : 0 ≤ K := by
    apply div_nonneg _ (sq_nonneg s)
    nlinarith [hs.1,hs.2,sq_nonneg (1-s)]
  have ht := (exp_decay (half_pos hr)).const_mul K
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with N hsmall
  intro hN μ β D hrep v hv
  let _ := mixtureGibbsLaw_probability hN μ β D
  have hrep' : ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real
      (replicaOverlapEvent (s^2/2)) ≤ Real.exp (-r*N) :=
    (measureReal_mono (fun z hz => lt_of_le_of_lt hε hz)).trans hrep
  have hcap := cap_mass_sq_le_replica_mass hN (mixtureGibbsLaw μ β D)
    (gibbsLaw_support hN β (fieldOfMixture μ D)) v ((onSphere_iff_norm_sq v).mp hv) hs
  have he : K*Real.exp (-r*N) = (K*Real.exp (-(r/2)*N))*Real.exp (-(r/2)*N) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hbound : ((mixtureGibbsLaw μ β D).real (cap v s))^2 ≤ Real.exp (-(r/2)*N) := by
    calc
      _ ≤ K*Real.exp (-r*N) := hcap.trans (mul_le_mul_of_nonneg_left hrep' hK)
      _ = _ := he
      _ ≤ _ := mul_le_of_le_one_left (Real.exp_pos _).le hsmall.le
  have hsquare : (Real.exp (-(r/4)*N))^2 = Real.exp (-(r/2)*N) := by
    rw [sq,← Real.exp_add]
    congr 1
    ring
  rw [← hsquare] at hbound
  exact (sq_le_sq₀ measureReal_nonneg (Real.exp_pos _).le).mp hbound

/-- All five source conclusions are derived simultaneously from literal
restricted-partition and replica events. The observable, good Gibbs set,
spectral index, time horizon and information constant are chosen internally.
These are primitive finite-volume model events, not source conclusions. -/
theorem constructed_memory_eventually (μ : FiniteMixture) (β : ℝ)
    (J G δ q₁ q₂ a ε b r : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hgap : 4*δ < G) (ha : 0 < a)
    (hq₁ : q₁ ∈ Ioo (0 : ℝ) 1) (hq : q₁ < q₂)
    (hε : 0 ≤ ε) (hb : 0 ≤ b) (hr : 0 < r)
    (hmargin : Real.sqrt b + Real.sqrt ε < q₁)
    (hεcap : ε ≤ (q₁/4)^2/2) (hδr : 4*δ < r/4) :
    ∃ κ γ aM cM CM : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < aM ∧ 0 < cM ∧ 0 < CM ∧
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 2 ≤ N) (F q w : ℝ) (D : Disorder N μ.maxDegree),
        q₂ ≤ q-w →
        D ∈ goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w
          (Real.exp (-a*N)) →
        ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real
          (replicaOverlapEvent ε) ≤ Real.exp (-r*N) →
        MemoryConclusions hN μ β D b κ γ aM cM CM := by
  obtain ⟨CE,cE,hCE,hcE,hcEq,hBuild⟩ :=
    sourceObservable_on_goodReference_event_eventually J G δ q₁ q₂ a 0
      hJ hδ hgap ha hq₁.1 hq hq₁.1
  obtain ⟨_CP,cP,_hCP,hcP,hcPEq,hPlateau⟩ :=
    constructed_plateau_eventually J G δ q₁ q₂ a ε b r
      hJ hδ hgap ha hq₁.1 hq hε hb hr hmargin
  let γ := cE/8
  let κ := (r/4-4*δ)/2
  let θ := min a (r/4)
  let aM := min a (min γ θ)
  let KX := startingErrorConstant CE q₁
  let KT := capErrorConstant (q₁/4)
  let CM := max (1+KX) (1+KT)
  have hqPos : 0 < q₁ := hq₁.1
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hκc : κ < r/4-4*δ := by dsimp [κ]; linarith
  have hθ : 0 < θ := lt_min ha (by positivity)
  have hAM : 0 < aM := lt_min ha (lt_min hγ hθ)
  have hKX : 0 ≤ KX := by dsimp [KX,startingErrorConstant]; positivity
  have hKT : 0 ≤ KT := by dsimp [KT,capErrorConstant]; positivity
  have hCM : 0 < CM := (show 0 < 1+KX by linarith).trans_le (le_max_left _ _)
  have hcSame : cP=cE := by rw [hcPEq,hcEq]
  have h2γ : 2*γ<cE := by dsimp [γ]; linarith
  have hγE : γ<cE := by dsimp [γ]; linarith
  have h4γ : 4*γ≤cE := by dsimp [γ]; linarith
  have hcGap : cE≤G-4*δ := by
    rw [hcEq]
    linarith [min_le_left (G-4*δ) a]
  have hs : q₁/4 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity,by linarith [hq₁.2]⟩
  have hFrame := cap_indicator_index_eventually (J := J) hq hκ hκc (h2γ.trans_le hcGap)
  have hProj := hPlateau (2*γ) γ (by rw [hcSame]; exact h2γ) (by rw [hcSame]; exact hγE)
  have hCaps := uniform_caps_of_replica_eventually hs hεcap hr
  have hTrap := quantitative_trap_eventually μ β (a := a) (c₀ := r/4)
    hγ hθ hCE.le hq₁.1 hs.1
    (show q₁/4≤q₁/2 by linarith [hq₁.1]) (min_le_left _ _) (min_le_right _ _)
  refine ⟨κ,γ,aM,θ/4,CM,hκ,hγ,hAM,by positivity,hCM,?_⟩
  filter_upwards [hBuild,hProj,hCaps,hFrame,hTrap,
    (exp_decay ha).eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))]
    with N hBuild hProj hCaps hFrame hTrap hsmall
  intro hN F q w D hcore hD hrep
  have hN1 : 1 ≤ N := by omega
  let _ := mixtureGibbsLaw_probability hN1 μ β D
  let _ := gibbsLaw_probability hN1 β (fieldOfMixture_contDiff μ D).continuous
  let _ := gibbsLaw_probability hN1 β (field_contDiff (mixtureCoefficients μ) D).continuous
  let S := sourceGoodSet (mixtureCoefficients μ) β F J G δ q₁ q₂ q w D
  let B := sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂
  obtain ⟨hSm,hSs,hBad,hBs,hB,hEnergy,hAlign,_hMean⟩ :=
    hBuild μ.maxDegree (mixtureCoefficients μ) β F q w D hcore hD
  have hCap := hCaps hN1 μ β D hrep
  have hMass : 1/2 ≤ (mixtureGibbsLaw μ β D).real S := by
    have hadd := probReal_add_probReal_compl (μ := mixtureGibbsLaw μ β D) hSm
    change (mixtureGibbsLaw μ β D).real Sᶜ ≤ Real.exp (-a*N) at hBad
    linarith
  have hEigen := hFrame hN β (fieldOfMixture μ D)
    ((fieldOfMixture_contDiff μ D).of_le (by simp)) S hSm hMass
    (fun u hu => (goodReferenceSet_cap_core_collar hN1 (mixtureCoefficients μ)
      β F J G δ q₁ q₂ q w D hD.1 hu).1)
    (fun u hu => ((goodReferenceSet_cap_core_collar hN1 (mixtureCoefficients μ)
      β F J G δ q₁ q₂ q w D hD.1 hu).2.1).trans
        (measureReal_mono (coreBand_subset_cap u q w q₂ hcore)))
    (fun u hu => (goodReferenceSet_cap_core_collar hN1 (mixtureCoefficients μ)
      β F J G δ q₁ q₂ q w D hD.1 hu).2.2)
    (fun v hv => (measureReal_mono (show cap v q₁ ⊆ cap v (q₁/4) from
      fun y hy => (show q₁/4≤q₁ by linarith [hq₁.1]).trans hy)).trans (hCap v hv))
  obtain ⟨hProjection,hCorrelation⟩ := hProj hN μ β F q w D hcore hD hrep
  have hEnergy' : vectorDirichletEnergy β (potential μ D) B ≤ CE*Real.exp (-4*γ*N) := by
    apply hEnergy.trans
    apply mul_le_mul_of_nonneg_left _ hCE.le
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hCap' : ∀ v, OnSphere v → (mixtureGibbsLaw μ β D).real (cap v (q₁/4)) ≤
      (2/(q₁/4))*Real.exp (-(r/4)*N) := by
    intro v hv
    apply (hCap v hv).trans
    apply le_mul_of_one_le_left (Real.exp_pos _).le
    exact (le_div_iff₀ hs.1).mpr (by linarith [hq₁.2])
  obtain ⟨X,hXm,hXs,hXBad,hTV,hMI⟩ := hTrap D B (hBs.of_le (by simp)) S hSm
    hEnergy' hBad hCap' (fun y _ => hB y) (fun y hy _ => (hAlign y hy).2)
  have hAMa : aM≤a := min_le_left _ _
  have hAMγ : aM≤γ := (min_le_right _ _).trans (min_le_left _ _)
  have hAMθ : aM≤θ := (min_le_right _ _).trans (min_le_right _ _)
  have hExp (z : ℝ) (hz : aM≤z) : Real.exp (-z*N)≤Real.exp (-aM*N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) (by positivity))
  have hXBad' : (mixtureGibbsLaw μ β D).real Xᶜ ≤ CM*Real.exp (-aM*N) := by
    apply hXBad.trans
    change Real.exp (-a*N)+KX*Real.exp (-2*γ*N) ≤ CM*Real.exp (-aM*N)
    have h2Exp : Real.exp (-2*γ*N)≤Real.exp (-aM*N) := by
      simpa only [neg_mul] using hExp (2*γ) (by linarith)
    calc
      _ ≤ Real.exp (-aM*N)+KX*Real.exp (-aM*N) :=
        add_le_add (hExp a hAMa)
          (mul_le_mul_of_nonneg_left h2Exp hKX)
      _ = (1+KX)*Real.exp (-aM*N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  refine ⟨hEigen,hProjection,hCorrelation,⟨X,hXm,hXs,?_,?_⟩,?_⟩
  · have hadd := probReal_add_probReal_compl (μ := mixtureGibbsLaw μ β D) hXm
    linarith
  · intro x hx t ht
    have herror : Real.exp (-γ*N)+KT*Real.exp (-θ*N)≤CM*Real.exp (-aM*N) := by
      calc
        _ ≤ Real.exp (-aM*N)+KT*Real.exp (-aM*N) :=
          add_le_add (hExp γ hAMγ) (mul_le_mul_of_nonneg_left (hExp θ hAMθ) hKT)
        _ = (1+KT)*Real.exp (-aM*N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have htV := (hTV x hx t ht).1
    dsimp [KT] at herror
    linarith
  · intro t _ht0 ht
    simpa only [div_mul_eq_mul_div] using hMI t ht

end
end SlowEquilibration.SphericalMemoryAssembly
