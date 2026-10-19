-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceInitialPairingTransfer
public import SlowEquilibration.ConditionedEntranceSourceJointRepresentatives
public import SlowEquilibration.ConditionedEntranceSmoothKilledBounds
public import SlowEquilibration.SphericalGibbsEquivalentMeasures

/-! Any chosen measurable physical killed resolvent transfers the uniform-start initial law to the original
Gibbs reference pairing of the jointly measurable physical killed resolvent. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem physical_pair_integrable_of_ac {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (ν : Measure (Vector N × Vector N)) [IsFiniteMeasure ν]
    (hν : ν ≪ (sphereLaw N).prod (gibbsLaw N β H))
    {f : Vector N × Vector N → ℝ} (hf : Continuous f) : Integrable f ν := by
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ z : Vector N × Vector N
      ∂(sphereLaw N).prod (gibbsLaw N β H),
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [gibbsLaw_support hN β H] with x hx
    exact ⟨hu,hx⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs.filter_mono hν.ae_le] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

/-- The source's actual first axis moment controls the change from a
uniform initial spin to the reference initial density, when the test is
the physical positive-rate killed resolvent for every spherical axis.
The normalizer is the single global source partition mass. -/
theorem actual_mixedSource_uniformKilledResolvent_reference_transfer_any
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ) (hα : 0 < α),
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      ∀ (θr : ℝ≥0), 0 < θr →
      ∀ (U₀ : SourceParameters (n+1) μ × Vector (n+1) → ℝ),
        StronglyMeasurable U₀ →
        (∀ (u : Vector (n+1)) (hu : OnSphere u),
          let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
            μ hnp Q hQ hQ1 α hα χ hχ (J,(u,(e,k))) hu
          (fun x => U₀ ((J,(u,(e,k))),x)) =ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            rateLaplace D β (PhysicalHitting.capKilling α u)
              (PhysicalHitting.capKilling_contDiff α u).continuous
              (PhysicalHitting.capKilling_nonneg α u) θr
              (killingVector D β (PhysicalHitting.capKilling α u)
                (PhysicalHitting.capKilling_contDiff α u).continuous)) →
      let H₀ := fieldOfMixture μ J
      let H : Vector (n+1) → Vector (n+1) → ℝ := fun u x =>
        sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (H z.1 z.2 - H₀ z.2)
      let f₀ : Vector (n+1) → ℝ := fun x => (gibbsDensity (n+1) β H₀ x)⁻¹
      let M := ∫ z, Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      let U : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        U₀ ((J,(z.1,(e,k))),z.2)
      (∫ u, ∫ x, U (u,x) ∂sphereLaw (n+1) ∂sphereLaw (n+1)) ≤
        (∫ z, f₀ z.2 * U z
          ∂normalizedTilt ((sphereLaw (n+1)).prod
            (gibbsLaw (n+1) β H₀)) w M) +
          4 * (C * ((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)) := by
  obtain ⟨C,hC,hL1⟩ := actual_mixedSource_globalInitialDensity_l1_bound
    μ hd hQ hnp hB hβ
  refine ⟨C,hC,?_⟩
  filter_upwards [hL1] with n hn
  intro J hJ α hα hαsmall χ hχ hχb hχR e k he hk θr hθr U₀ hU₀ hUphys
  dsimp only
  let N := n+1
  have hN : 1 ≤ N := by omega
  let H₀ : Vector N → ℝ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun u x =>
    sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x
  let w : Vector N × Vector N → ℝ := fun z => β * (H z.1 z.2 - H₀ z.2)
  let f₀ : Vector N → ℝ := fun x => (gibbsDensity N β H₀ x)⁻¹
  let π := gibbsLaw N β H₀
  let σ := sphereLaw N
  let ν₀ := σ.prod π
  let M := ∫ z, Real.exp (w z) ∂ν₀
  let ν := normalizedTilt ν₀ w M
  let : IsProbabilityMeasure σ := sphereLaw_probability N
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector N × Vector N =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hew : Integrable (fun z => Real.exp (w z)) ν₀ :=
    physical_pair_integrable_of_ac hN β H₀ hH₀ ν₀ (by rfl) hw.rexp
  have hM : 0 < M := integral_exp_pos hew
  let : IsProbabilityMeasure ν := normalizedTilt_probability ν₀ w hM hew rfl
  let hν : ν ≪ ν₀ := withDensity_absolutelyContinuous _ _
  have hf₀c : Continuous f₀ :=
    (gibbsDensity_continuous β hH₀).inv₀
      (fun x => (gibbsDensity_pos hN β hH₀ x).ne')
  have hfc : Continuous (fun z : Vector N × Vector N => f₀ z.2) :=
    hf₀c.comp continuous_snd
  have hqc : Continuous (fun z : Vector N × Vector N =>
      M * Real.exp (-w z) * f₀ z.2) :=
    (continuous_const.mul (hw.neg.rexp)).mul hfc
  have hf : Integrable (fun z : Vector N × Vector N => f₀ z.2) ν :=
    physical_pair_integrable_of_ac hN β H₀ hH₀ ν hν hfc
  have hq : Integrable (fun z : Vector N × Vector N =>
      M * Real.exp (-w z) * f₀ z.2) ν :=
    physical_pair_integrable_of_ac hN β H₀ hH₀ ν hν hqc
  let U : Vector N × Vector N → ℝ := fun z => U₀ ((J,(z.1,(e,k))),z.2)
  have hU : StronglyMeasurable U := hU₀.comp_measurable (by fun_prop)
  have hUslice (u : Vector N) (hu : OnSphere u) :
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
        (J,(u,(e,k))) hu
      let κ := PhysicalHitting.capKilling α u
      (fun x => U (u,x)) =ᵐ[gibbsLaw N β (H u)]
        rateLaplace D β κ (PhysicalHitting.capKilling_contDiff α u).continuous
          (PhysicalHitting.capKilling_nonneg α u) θr
          (killingVector D β κ (PhysicalHitting.capKilling_contDiff α u).continuous) := by
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u,(e,k))) hu
    have hDham : D.hamiltonian = H u := rfl
    rw [← hDham]
    simpa only [U,N,D] using hUphys u hu
  have hUbound (u : Vector N) (hu : OnSphere u) :
      ∀ᵐ x ∂π, 0 ≤ U (u,x) ∧ U (u,x) ≤ 1 := by
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u,(e,k))) hu
    let κ := PhysicalHitting.capKilling α u
    have hκ := (PhysicalHitting.capKilling_contDiff α u).continuous
    have hκ0 := PhysicalHitting.capKilling_nonneg α u
    have hκ1 : ∀ x, ‖κ x‖ ≤ (1 : ℝ≥0) := by
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 x)]
      exact PhysicalHitting.capKilling_le_one hα u x
    have hπ : π ≪ gibbsLaw N β D.hamiltonian :=
      gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D.hamiltonian H₀
        D.hamiltonian_contDiff.continuous
    have hu' := hUslice u hu
    have hb := rateLaplace_killing_unit_interval D β κ hκ hκ0 1 hκ1 θr hθr
    filter_upwards [hu'.filter_mono hπ.ae_le, hb.filter_mono hπ.ae_le] with x hx hb
    change U (u,x) = _ at hx
    rw [hx]
    exact hb
  have hUb : ∀ᵐ z ∂ν₀, 0 ≤ U z ∧ U z ≤ 1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    exact hUbound u ((onSphere_iff_norm_sq u).mpr hu)
  have hUbν : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1 := hUb.filter_mono hν.ae_le
  have hUnorm : ∀ᵐ z ∂ν₀, ‖U z‖ ≤ 1 := hUb.mono (fun z hz => by
    rw [Real.norm_eq_abs,abs_of_nonneg hz.1]
    exact hz.2)
  have hfbase : Integrable (fun z : Vector N × Vector N => f₀ z.2) ν₀ :=
    physical_pair_integrable_of_ac hN β H₀ hH₀ ν₀ (by rfl) hfc
  have hfiBase : Integrable (fun z : Vector N × Vector N => f₀ z.2 * U z) ν₀ :=
    hfbase.mul_bdd hU.aestronglyMeasurable hUnorm
  have hUniform : (∫ z, (M * Real.exp (-w z) * f₀ z.2) * U z ∂ν) =
      ∫ u, ∫ x, U (u,x) ∂σ ∂σ := by
    rw [normalizedTilt_initial_pairing ν₀ w hw.measurable hM
      (fun z => f₀ z.2) U]
    rw [integral_prod _ hfiBase]
    apply integral_congr_ae
    exact .of_forall fun u => by
      change (∫ x, f₀ x * U (u,x) ∂gibbsLaw N β H₀) =
        ∫ x, U (u,x) ∂sphereLaw N
      rw [integral_gibbsLaw hN β hH₀]
      apply integral_congr_ae
      exact .of_forall fun x => by
        change gibbsDensity N β H₀ x * (f₀ x * U (u,x)) = U (u,x)
        rw [← mul_assoc]
        rw [show gibbsDensity N β H₀ x * f₀ x = 1 from
          mul_inv_cancel₀ (gibbsDensity_pos hN β hH₀ x).ne', one_mul]
  have hL1bound : (∫ z, |M * Real.exp (-w z) * f₀ z.2 - f₀ z.2| ∂ν) ≤
      4 * (C * ((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)) := by
    simpa only [N,H₀,H,w,f₀,M,ν,ν₀,σ,π] using
      (hn J hJ α hα hαsmall χ hχ hχb hχR e k he hk)
  have htransfer := initialDensity_pairing_le_reference_add_l1 ν
      (fun z => M * Real.exp (-w z) * f₀ z.2) (fun z => f₀ z.2)
      U hq hf hU.aestronglyMeasurable hUbν
  have ht : (∫ z, (M * Real.exp (-w z) * f₀ z.2) * U z ∂ν) ≤
        (∫ z, f₀ z.2 * U z ∂ν) +
          4 * (C * ((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)) := by
    linarith
  rw [hUniform] at ht
  simpa only [N,H₀,H,w,f₀,M,ν,ν₀,σ,π] using ht

end SlowEquilibration.ConditionedEntrance
