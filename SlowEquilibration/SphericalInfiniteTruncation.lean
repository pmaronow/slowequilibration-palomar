-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteContinuousField
public import SlowEquilibration.IntegrableSummableSeries

/-! Actual finite-degree truncation under the common infinite disorder, with
an expected uniform error that is o(N), uniformly over the dimension. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal first P homogeneous blocks (degrees 2 through P+1). -/
def partialField {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) (x : Vector N) : ℝ :=
  ∑ p∈Finset.range P,block μ p J x

def tailContinuous {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) : C(PhysicalBall N,ℝ) :=
  ∑' q,blockContinuous μ (q+P) J

/-- A deterministic summable source coefficient tail. -/
def truncationTail (μ : InfiniteMixture) (P : ℕ) : ℝ :=
  ∑' q,((q+P+2:ℕ):ℝ)^(5/2:ℝ)*Real.sqrt (μ.coeff (q+P+2))

theorem truncationTail_nonneg (μ : InfiniteMixture) (P : ℕ) : 0≤truncationTail μ P :=
  tsum_nonneg (fun _ => by positivity)

theorem truncationTail_tendsto_zero (μ : InfiniteMixture) :
    Tendsto (truncationTail μ) atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun p => ((p+2:ℕ):ℝ)^(5/2:ℝ)*Real.sqrt (μ.coeff (p+2))
  have hs : Summable f := μ.summable_shifted_weighted_sqrt (s := 5/2) le_rfl
  have he (P : ℕ) : truncationTail μ P=(∑' p,f p)-∑ p∈Finset.range P,f p := by
    have hh := hs.sum_add_tsum_nat_add P
    change (∑' q,f (q+P))=_
    linarith
  change Tendsto (fun P => truncationTail μ P) atTop (𝓝 0)
  simp_rw [he]
  have ht : Tendsto (fun P => (∑' p,f p)-∑ p∈Finset.range P,f p) atTop
      (𝓝 ((∑' p,f p)-(∑' p,f p))) := tendsto_const_nhds.sub hs.tendsto_sum_tsum_nat
  simpa only [sub_self] using ht

theorem blockContinuous_integrable {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (p : ℕ) :
    Integrable (blockContinuous (N := N) μ p) (disorderLaw N) :=
  (blockJetEnvelope_integrable hN μ 0 p).mono'
    (blockContinuous_continuous μ p).measurable.aestronglyMeasurable
    (.of_forall (blockContinuous_norm_le hN μ p))

theorem summable_integral_norm_blockContinuous {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) :
    Summable (fun p => ∫ J,‖blockContinuous μ p J‖ ∂disorderLaw N) := by
  apply (summable_blockJetEnvelope_integral_norm hN μ 0 (by omega)).of_nonneg_of_le
  · intro p
    exact integral_nonneg (fun _ => norm_nonneg _)
  · intro p
    apply integral_mono (blockContinuous_integrable hN μ p).norm
      (blockJetEnvelope_integrable hN μ 0 p).norm
    intro J
    dsimp only
    rw [Real.norm_of_nonneg (blockJetEnvelope_nonneg hN μ 0 p J)]
    exact blockContinuous_norm_le hN μ p J

theorem continuousField_integrable {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) :
    Integrable (continuousField (N := N) μ) (disorderLaw N) :=
  IntegrableSummableSeries.integrable_tsum (blockContinuous_integrable hN μ)
    (summable_integral_norm_blockContinuous hN μ)

theorem tailContinuous_integrable {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (P : ℕ) :
    Integrable (tailContinuous (N := N) μ P) (disorderLaw N) :=
  IntegrableSummableSeries.integrable_tsum (fun q => blockContinuous_integrable hN μ (q+P))
    ((summable_nat_add_iff P).2 (summable_integral_norm_blockContinuous hN μ))

theorem tailContinuous_eq_sub {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (P : ℕ)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) (x : PhysicalBall N) :
    tailContinuous μ P J x=field μ J x-partialField μ P J x := by
  have hs := (summable_blockContinuous_norm hN μ J hJ).of_norm
  have hh := congrArg (fun F : C(PhysicalBall N,ℝ) => F x) (hs.sum_add_tsum_nat_add P)
  simp only [ContinuousMap.add_apply,ContinuousMap.sum_apply] at hh
  change (∑ p∈Finset.range P,block μ p J x)+tailContinuous μ P J x=continuousField μ J x at hh
  rw [continuousField_apply hN μ J hJ x] at hh
  dsimp [partialField]
  linarith

theorem tailContinuous_expected_norm_le {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (P : ℕ) :
    (∫ J,‖tailContinuous μ P J‖ ∂disorderLaw N)≤8*(N:ℝ)*truncationTail μ P := by
  let F : ℕ → Disorder N → ℝ := fun q J => blockJetEnvelope μ 0 (q+P) J
  have hi (q : ℕ) : Integrable (F q) (disorderLaw N) := blockJetEnvelope_integrable hN μ 0 (q+P)
  have hs : Summable (fun q => ∫ J,‖F q J‖ ∂disorderLaw N) :=
    (summable_nat_add_iff P).2 (summable_blockJetEnvelope_integral_norm hN μ 0 (by omega))
  have hiSum := IntegrableSummableSeries.integrable_tsum hi hs
  calc
    _ ≤ ∫ J,∑' q,F q J ∂disorderLaw N := by
      apply integral_mono_ae (tailContinuous_integrable hN μ P).norm hiSum
      filter_upwards [summableJetDisorder_ae hN μ] with J hJ
      have hsC := (summable_nat_add_iff P).2 (summable_blockContinuous_norm hN μ J hJ)
      have hsF := (summable_nat_add_iff P).2 (hJ 0 (by omega))
      exact (norm_tsum_le_tsum_norm hsC).trans
        (hsC.tsum_le_tsum (fun q => blockContinuous_norm_le hN μ (q+P) J) hsF)
    _ = ∑' q,∫ J,F q J ∂disorderLaw N :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ ≤ ∑' q,8*(N:ℝ)*(((q+P+2:ℕ):ℝ)^(5/2:ℝ)*Real.sqrt (μ.coeff (q+P+2))) := by
      have hsI : Summable (fun q => ∫ J,F q J ∂disorderLaw N) := by
        simpa only [F,Real.norm_of_nonneg (blockJetEnvelope_nonneg hN μ 0 _ _)] using hs
      apply hsI.tsum_le_tsum
      · intro q
        simpa only [F,mul_assoc] using blockJetEnvelope_mean_le hN μ 0 (q+P) (by omega)
      · exact ((summable_nat_add_iff P).2
          (μ.summable_shifted_weighted_sqrt (s := 5/2) le_rfl)).mul_left (8*(N:ℝ))
    _ = _ := by rw [tsum_mul_left];rfl

/-- The actual expected uniform truncation error divided by N goes to zero
uniformly in the dimension; this is the order of limits needed for pressure. -/
theorem expected_uniform_truncation_error_eventually (μ : InfiniteMixture) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ P in atTop,∀ N : ℕ,0<N →
      (∫ J,‖tailContinuous μ P J‖ ∂disorderLaw N)/(N:ℝ)≤ε := by
  have hh := (truncationTail_tendsto_zero μ).eventually (gt_mem_nhds (show (0:ℝ)<ε/8 by positivity))
  filter_upwards [hh] with P hP
  intro N hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  apply (div_le_iff₀ hNr).2
  calc
    _ ≤ 8*(N:ℝ)*truncationTail μ P := tailContinuous_expected_norm_le hN μ P
    _ ≤ ε*N := by nlinarith

end SlowEquilibration.SphericalInfiniteModel
