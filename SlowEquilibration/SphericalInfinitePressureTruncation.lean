-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteTruncation
public import SlowEquilibration.CompactSphereCarrier
public import SlowEquilibration.SphericalGibbs

/-! Literal infinite spherical pressure and its genuine finite-degree
approximation, with dimension-uniform expected error proved from the field. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The compact representative uses the actual normalized spherical measure. -/
def logPressure (N : ℕ) (μ : InfiniteMixture) (β : ℝ) (J : Disorder N) : ℝ :=
  ContinuousFieldPartition.logPartition (CompactSphereCarrier.law N) β (continuousField μ J)/N

def partialContinuous {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) : C(PhysicalBall N,ℝ) :=
  ∑ p∈Finset.range P,blockContinuous μ p J

def partialLogPressure (N : ℕ) (μ : InfiniteMixture) (β : ℝ) (P : ℕ) (J : Disorder N) : ℝ :=
  ContinuousFieldPartition.logPartition (CompactSphereCarrier.law N) β (partialContinuous μ P J)/N

def quenchedPressure (N : ℕ) (μ : InfiniteMixture) (β : ℝ) : ℝ :=
  ∫ J,logPressure N μ β J ∂disorderLaw N

def partialQuenchedPressure (N : ℕ) (μ : InfiniteMixture) (β : ℝ) (P : ℕ) : ℝ :=
  ∫ J,partialLogPressure N μ β P J ∂disorderLaw N

theorem field_measurable {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) :
    Measurable (field μ J) :=
  Measurable.tsum (fun p => (block_contDiff μ p J).continuous.measurable)

theorem logPressure_eq_literal {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (β : ℝ)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) :
    logPressure N μ β J=Real.log (partition N β (field μ J))/N := by
  unfold logPressure ContinuousFieldPartition.logPartition ContinuousFieldPartition.partition partition
  congr 2
  calc
    _ = ∫ x : CompactSphereCarrier.Carrier N,Real.exp (β*field μ J x) ∂CompactSphereCarrier.law N := by
      apply integral_congr_ae
      exact .of_forall (fun x => by dsimp only; rw [continuousField_apply hN μ J hJ x])
    _ = _ := CompactSphereCarrier.integral_coe hN (fun x => Real.exp (β*field μ J x))
      (Real.measurable_exp.comp (measurable_const.mul (field_measurable μ J)))

theorem partialLogPressure_eq_literal {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (β : ℝ)
    (P : ℕ) (J : Disorder N) :
    partialLogPressure N μ β P J=Real.log (partition N β (partialField μ P J))/N := by
  have hc : Continuous (partialField μ P J) :=
    continuous_finset_sum _ (fun p _ => (block_contDiff μ p J).continuous)
  have he : partialContinuous μ P J=
      ⟨fun x => partialField μ P J x,hc.comp continuous_subtype_val⟩ := by
    ext x
    simp [partialContinuous,partialField,blockContinuous]
  unfold partialLogPressure
  rw [he,CompactSphereCarrier.logPartition_eq_sphere hN β _ hc]
  rfl

private theorem compact_logPartition_integrable {N : ℕ} (hN : 0<N) (β : ℝ)
    (F : Disorder N → C(PhysicalBall N,ℝ)) (hF : Integrable F (disorderLaw N)) :
    Integrable (fun J => ContinuousFieldPartition.logPartition (CompactSphereCarrier.law N) β (F J))
      (disorderLaw N) := by
  letI := CompactSphereCarrier.law_probability hN
  let L := ContinuousFieldPartition.logPartition (CompactSphereCarrier.law N) β
  have hL := ContinuousFieldPartition.logPartition_lipschitz (CompactSphereCarrier.law N) β
  have h0 : L 0=0 := by
    simp [L,ContinuousFieldPartition.logPartition,ContinuousFieldPartition.partition]
  apply (hF.norm.const_mul |β|).mono' (hL.continuous.comp_aestronglyMeasurable hF.aestronglyMeasurable)
  exact .of_forall fun J => by
    have h := hL.norm_sub_le (F J) 0
    change ‖L (F J)-L 0‖≤|β| * ‖F J-0‖ at h
    simpa only [h0,sub_zero] using h

theorem logPressure_integrable {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (β : ℝ) :
    Integrable (logPressure N μ β) (disorderLaw N) :=
  (compact_logPartition_integrable hN β _ (continuousField_integrable hN μ)).div_const N

theorem partialLogPressure_integrable {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (β : ℝ) (P : ℕ) :
    Integrable (partialLogPressure N μ β P) (disorderLaw N) := by
  have hi : Integrable (partialContinuous (N := N) μ P) (disorderLaw N) := by
    unfold partialContinuous
    exact integrable_finsetSum (Finset.range P)
      (f := fun p J => blockContinuous (N := N) μ p J)
      (fun p _ => blockContinuous_integrable hN μ p)
  exact (compact_logPartition_integrable hN β _ hi).div_const N

theorem logPressure_truncation_error_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (β : ℝ) (P : ℕ) :
    ∀ᵐ J ∂disorderLaw N,|logPressure N μ β J-partialLogPressure N μ β P J|≤
      |β| *‖tailContinuous μ P J‖/N := by
  letI := CompactSphereCarrier.law_probability hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  filter_upwards [summableJetDisorder_ae hN μ] with J hJ
  have he : continuousField μ J-partialContinuous μ P J=tailContinuous μ P J := by
    have hh := (summable_blockContinuous_norm hN μ J hJ).of_norm.sum_add_tsum_nat_add P
    change partialContinuous μ P J+tailContinuous μ P J=continuousField μ J at hh
    exact eq_sub_of_add_eq' hh |>.symm
  have h := (ContinuousFieldPartition.logPartition_lipschitz (CompactSphereCarrier.law N) β).norm_sub_le
    (continuousField μ J) (partialContinuous μ P J)
  rw [he,Real.norm_eq_abs] at h
  dsimp [logPressure,partialLogPressure]
  rw [← sub_div,abs_div,abs_of_pos hNr]
  exact div_le_div_of_nonneg_right h hNr.le

theorem quenchedPressure_truncation_error {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (β : ℝ) (P : ℕ) :
    |quenchedPressure N μ β-partialQuenchedPressure N μ β P|≤8*|β| *truncationTail μ P := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  unfold quenchedPressure partialQuenchedPressure
  rw [← integral_sub (logPressure_integrable hN μ β) (partialLogPressure_integrable hN μ β P)]
  calc
    _ ≤ ∫ J,|logPressure N μ β J-partialLogPressure N μ β P J| ∂disorderLaw N :=
      abs_integral_le_integral_abs
    _ ≤ ∫ J,|β| *‖tailContinuous μ P J‖/N ∂disorderLaw N :=
      integral_mono_ae ((logPressure_integrable hN μ β).sub (partialLogPressure_integrable hN μ β P)).abs
        (((tailContinuous_integrable hN μ P).norm.const_mul |β|).div_const N)
        (logPressure_truncation_error_ae hN μ β P)
    _ = |β| *(∫ J,‖tailContinuous μ P J‖ ∂disorderLaw N)/N := by rw [integral_div,integral_const_mul]
    _ ≤ |β| *(8*N*truncationTail μ P)/N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (tailContinuous_expected_norm_le hN μ P)
        (abs_nonneg _)) hNr.le
    _ = _ := by field_simp <;> ring

end SlowEquilibration.SphericalInfiniteModel
