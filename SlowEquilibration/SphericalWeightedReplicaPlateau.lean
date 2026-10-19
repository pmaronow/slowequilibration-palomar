-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSourceObservablePlateau

@[expose] public section

/-! # Stronger spin plateaus from the actual reweighted two-replica moment

The missing stochastic input of source prop:pl-norm is isolated as the
literal overlap moment of the constructed overlap-weighted Gibbs law.
Its equality with the actual observable norm is proved here. Projection
and stationary correlation conclusions are derived, never assumed.
-/

namespace SlowEquilibration.SphericalWeightedReplicaPlateau
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalBarycenter SphericalPhysicalSpectral
open SphericalLaplaceIdentification SphericalCenteredObservables SphericalSpinProjection
open SphericalSpinCorrelation SphericalReplicaMagnetization SphericalSourceObservablePlateau
open SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal ENNReal
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def sourceWeightedReplicaMoment (μ : FiniteMixture) (β : ℝ) (D : Disorder N μ.maxDegree)
    (J δ q₁ q₂ : ℝ) : ℝ :=
  ∫ x, (∫ z : Vector N × Vector N, overlap z.1 z.2
    ∂(weightedLaw β (fieldOfMixture μ D) (sourceProfile J δ q₁ q₂) x).prod
      (weightedLaw β (fieldOfMixture μ D) (sourceProfile J δ q₁ q₂) x))
    ∂mixtureGibbsLaw μ β D

/-- The source norm is the genuine two-replica moment of the actual
normalized overlap-reweighted law, including exceptional references. -/
theorem sourceWeightedReplicaMoment_eq_norm (hN : 1  ≤  N) (μ : FiniteMixture) (β : ℝ)
    (D : Disorder N μ.maxDegree) (J δ q₁ q₂ : ℝ) :
    sourceWeightedReplicaMoment μ β D J δ q₁ q₂ =
      ∫ x, ‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2 ∂mixtureGibbsLaw μ β D := by
  apply integral_congr_ae
  exact .of_forall fun x => (barycenter_norm_sq_eq hN β (fieldOfMixture_contDiff μ D).continuous
    (sourceProfile_contDiff J δ q₁ q₂) x).symm

theorem spin_projection_with_norm_bound (hN : 2  ≤  N) (μ : FiniteMixture) (β : ℝ)
    (D : Disorder N μ.maxDegree) (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, OnSphere x → ‖B x‖ ≤ 1) {a m b Λ : ℝ}
    (hm : 0 < m) (hb : 0 ≤ b) (hΛ : 0 < Λ)
    (ha : a ≤ ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β D)
    (hNorm : (∫ x, ‖B x‖^2 ∂mixtureGibbsLaw μ β D) ≤ m)
    (hMargin : Real.sqrt b*Real.sqrt m ≤ a-‖mean μ D β spin‖-
      Real.sqrt (vectorDirichletEnergy β (potential μ D) B/Λ)) :
    b ≤ ‖vectorCutoff hN μ D β Λ
      (centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp)))‖^2 := by
  let Z := centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp))
  let C := centeredL2 (show 1 ≤ N by omega) μ D β B hBs
  have hZ := centered_spin_norm_le_one (show 1 ≤ N by omega) μ D β
  have hInner := centered_spin_alignment_lower (show 1 ≤ N by omega) μ D β B hBs hB ha
  have hAlign := smooth_projection_alignment hN μ D β B hBs Z hΛ
  have hC : ‖C‖ ≤ Real.sqrt m := by
    apply Real.le_sqrt_of_sq_le
    have hv := centeredL2_variance (show 1 ≤ N by omega) μ D β B hBs
    change ‖C‖^2=(∫ x, ‖B x‖^2 ∂mixtureGibbsLaw μ β D)-‖mean μ D β B‖^2 at hv
    linarith [sq_nonneg ‖mean μ D β B‖]
  have hError : ‖Z‖*Real.sqrt (vectorDirichletEnergy β (potential μ D) B/Λ) ≤ 
      Real.sqrt (vectorDirichletEnergy β (potential μ D) B/Λ) :=
    mul_le_of_le_one_left (Real.sqrt_nonneg _) hZ
  have hLower : Real.sqrt b*Real.sqrt m ≤ ‖vectorCutoff hN μ D β Λ Z‖*‖C‖ := by
    have hBase : a-‖mean μ D β spin‖-Real.sqrt (vectorDirichletEnergy β (potential μ D) B/Λ) ≤ 
        inner ℝ Z C-‖Z‖*Real.sqrt (vectorDirichletEnergy β (potential μ D) B/Λ) := by
      linarith
    exact hMargin.trans (hBase.trans hAlign)
  have hProduct := hLower.trans (mul_le_mul_of_nonneg_left hC (norm_nonneg _))
  have hProjection := (mul_le_mul_iff_left₀ (Real.sqrt_pos.mpr hm)).mp hProduct
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg b) hProjection 2
  rwa [Real.sq_sqrt hb] at hsquare

private theorem exp_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.exp (-a*N)) atTop (𝓝 (0 : ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply,neg_mul]

/-- Exact deterministic reduction of source thm:main-plateau(ii),(iii).
The norm obligation is stated as an actual reweighted two-replica moment;
the genuine transverse-pressure/contiguity proof remains separate. -/
theorem constructed_weightedReplica_plateau_eventually (J G δ q₁ q₂ a ε bP bC r m : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hGap : 4*δ < G) (ha : 0 < a)
    (hq₁ : 0 < q₁) (hq : q₁ < q₂) (hε : 0 ≤ ε) (hbP : 0 ≤ bP)
    (hbC : bC < bP) (hr : 0 < r) (hm : 0 < m)
    (hMargin : Real.sqrt bP*Real.sqrt m+Real.sqrt ε < q₁) :
    ∃ cE : ℝ, 0 < cE ∧ cE=min (G-4*δ) a/2 ∧
      ∀ γ : ℝ, 0 < γ → 2*γ < cE →
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 2 ≤ N) (μ : FiniteMixture) (β F q w : ℝ)
        (D : Disorder N μ.maxDegree), q₂ ≤ q-w →
        D∈goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a*N)) →
        ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real
          (replicaOverlapEvent ε) ≤ Real.exp (-r*N) →
        sourceWeightedReplicaMoment μ β D J δ q₁ q₂ ≤ m →
        bP ≤ ‖vectorCutoff hN μ D β (Real.exp (-(2*γ)*N))
          (centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp)))‖^2 ∧
        ∀ t ≤ plateauTime γ N, bC ≤ connectedSpinCorrelation μ D β t := by
  obtain ⟨CE,cE,hCE,hcE,hcEq,hBuild⟩ :=
    sourceObservable_on_goodReference_event_eventually J G δ q₁ q₂ a 0
      hJ hδ hGap ha hq₁ hq hq₁
  refine ⟨cE,hcE,hcEq,?_⟩
  intro γ hγ hγE
  have h1 : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ))) atTop (𝓝 (0:ℝ)) := by
    simpa only [neg_one_mul] using exp_decay (show (0 : ℝ) < 1 by norm_num)
  have hErrors := ((((h1.add (exp_decay ha)).const_mul (1+q₁)).add (exp_decay (half_pos hr))).add
    (((exp_decay (sub_pos.mpr hγE)).const_mul CE).sqrt))
  simp only [add_zero,mul_zero,Real.sqrt_zero] at hErrors
  have hsmall := hErrors.eventually (gt_mem_nhds
    (show 0 < q₁-Real.sqrt bP*Real.sqrt m-Real.sqrt ε by linarith))
  have hCorr : Tendsto (fun N : ℕ => Real.exp (-Real.exp (-γ*N))*bP) atTop (𝓝 bP) := by
    have h := ((Real.continuous_exp.tendsto (-(0:ℝ))).comp ((exp_decay hγ).neg)).mul_const bP
    simpa only [neg_zero,Real.exp_zero,one_mul,Function.comp_apply] using h
  filter_upwards [hBuild,hsmall,hCorr.eventually (lt_mem_nhds hbC)] with N hBuild hErrors hCorr
  intro hN μ β F q w D hCore hD hReplica hMoment
  obtain ⟨_hSm,_hSs,_hBad,hBs,hB,hEnergy,_hAlign,hMean⟩ :=
    hBuild μ.maxDegree (mixtureCoefficients μ) β F q w D hCore hD
  let B := sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂
  have hBs' : ContDiff ℝ 1 B := hBs.of_le (by simp)
  have hMag := mixture_magnetization_le_of_replica (show 1 ≤ N by omega) μ D β hε hReplica
  have hRatio : vectorDirichletEnergy β (potential μ D) B/Real.exp (-(2*γ)*N) ≤ 
      CE*Real.exp (-(cE-2*γ)*N) := by
    apply (div_le_div_of_nonneg_right hEnergy (Real.exp_pos _).le).trans_eq
    rw [mul_div_assoc,← Real.exp_sub]
    congr 2
    ring
  have hSqrt := Real.sqrt_le_sqrt hRatio
  have hNorm : (∫ x, ‖B x‖^2 ∂mixtureGibbsLaw μ β D) ≤ m := by
    rw [← sourceWeightedReplicaMoment_eq_norm (show 1 ≤ N by omega) μ β D J δ q₁ q₂]
    exact hMoment
  have hProjection := spin_projection_with_norm_bound hN μ β D B hBs'
    (Λ := Real.exp (-(2*γ)*N))
    (fun x _ => hB x) hm hbP (Real.exp_pos _)
    hMean hNorm (by linarith)
  refine ⟨hProjection,?_⟩
  have hProduct : (plateauTime γ N : ℝ)*Real.exp (-(2*γ)*N)=Real.exp (-γ*N) := by
    change Real.exp (γ*N)*Real.exp (-(2*γ)*N)=Real.exp (-γ*N)
    rw [← Real.exp_add]
    congr 1
    ring
  intro t ht
  have hPhysical := projected_connected_correlation_uniform hN μ D β
    (Λ := Real.exp (-(2*γ)*N)) (Real.exp_pos _).le
    (plateauTime γ N) t ht
  rw [neg_mul, hProduct] at hPhysical
  exact hCorr.le.trans ((mul_le_mul_of_nonneg_left hProjection (Real.exp_pos _).le).trans hPhysical)

end
end SlowEquilibration.SphericalWeightedReplicaPlateau
