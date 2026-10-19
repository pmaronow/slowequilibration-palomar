-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceReferenceMassTwo
public import SlowEquilibration.ConditionedEntranceNormalizedHazardMass
public import SlowEquilibration.ConditionedEntrancePhysicalCutoffEnergy
public import SlowEquilibration.ConditionedEntranceSourceJointKilling

/-! Actual unperturbed source reference resolvent in the globally tilted
physical cap hazard. The frozen-axis mass two is used exactly. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalAging HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

/-- The normalized physical source cap hazard weighted by the genuine
base reference resolvent costs four times the actual cutoff-energy factor
and the uniform-axis cap mean. The only two quantitative premises are the
physical normalizer lower bound and physical axis-tail bound, proved in
the dimension-dependent source application. -/
theorem sourceReference_normalized_capKilling_le
    (D : SourceData N) (β : ℝ) (hβ : 0 ≤ β)
    (θr : ℝ≥0) (hθr : 0 < θr)
    (hJ : D.disorder ∈ regularDisorder)
    {hbar kbar B R : ℝ}
    (hh : |D.energyMark| ≤ hbar) (hk : |D.radialMark| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s, |D.cutoff s| ≤ B)
    (hχR : ∀ s, R < |s| → D.cutoff s = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (haxis : ∀ x : Vector N, OnSphere x →
      (∫ u, PhysicalHitting.capKilling D.cutoffScale u x ∂sphereLaw N) ≤ K) :
    let π := gibbsLaw N β D.baseData.hamiltonian
    let w : Vector N × Vector N → ℝ := fun z =>
      β * (sourceSmoothCutoffField D.mixture D.Q D.Q_pos D.nonpure
        D.disorder z.1 D.energyMark D.radialMark D.cutoffScale D.cutoff z.2 -
          D.baseData.hamiltonian z.2)
    let M := ∫ z, Real.exp (w z) ∂((sphereLaw N).prod π)
    1/2 ≤ M →
    (∫ z, PhysicalHitting.capKilling D.cutoffScale z.1 z.2 *
        sourceReferencePositivePart D β θr z.2
      ∂normalizedTilt ((sphereLaw N).prod π) w M) ≤
        4 * Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant
          D.mixture D.Q hbar kbar B R * (N : ℝ) *
            D.cutoffScale^D.mixture.minDegree) * K := by
  dsimp only
  let π := gibbsLaw N β D.baseData.hamiltonian
  let θ := sphereLaw N
  let w : Vector N × Vector N → ℝ := fun z =>
    β * (sourceSmoothCutoffField D.mixture D.Q D.Q_pos D.nonpure
      D.disorder z.1 D.energyMark D.radialMark D.cutoffScale D.cutoff z.2 -
        D.baseData.hamiltonian z.2)
  let κ : Vector N × Vector N → ℝ := fun z =>
    PhysicalHitting.capKilling D.cutoffScale z.1 z.2
  let F : Vector N → ℝ := sourceReferencePositivePart D β θr
  let W := Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant
    D.mixture D.Q hbar kbar B R * (N : ℝ) *
      D.cutoffScale^D.mixture.minDegree)
  let M := ∫ z, Real.exp (w z) ∂θ.prod π
  intro hM
  let : IsProbabilityMeasure θ := sphereLaw_probability N
  let : IsProbabilityMeasure π := gibbsLaw_probability D.dimension_ge_one β
    D.baseData.hamiltonian_contDiff.continuous
  have hH : Continuous (fun z : Vector N × Vector N =>
      sourceSmoothCutoffField D.mixture D.Q D.Q_pos D.nonpure
        D.disorder z.1 D.energyMark D.radialMark D.cutoffScale D.cutoff z.2) :=
    (sourceSmoothCutoffField_jointContinuous D.mixture D.Q D.Q_pos D.nonpure
      D.cutoffScale D.cutoff D.cutoff_smooth.continuous).comp
      (show Continuous (fun z : Vector N × Vector N =>
        ((D.disorder,(z.1,(D.energyMark,D.radialMark))),z.2)) by fun_prop)
  have hw : Continuous w :=
    (hH.sub (D.baseData.hamiltonian_contDiff.continuous.comp continuous_snd)).const_mul β
  have hκc : Continuous κ := capKilling_jointContinuous D.cutoffScale
  have hκ0 (z : Vector N × Vector N) : 0 ≤ κ z :=
    PhysicalHitting.capKilling_nonneg D.cutoffScale z.1 z.2
  have hκ1 (z : Vector N × Vector N) : κ z ≤ 1 :=
    PhysicalHitting.capKilling_le_one D.cutoffScale_pos z.1 z.2
  have hF0 (x : Vector N) : 0 ≤ F x := le_max_left _ _
  have hiF : Integrable F π := sourceReferencePositivePart_integrable D β θr
  have hFprod : Integrable (fun z : Vector N × Vector N => F z.2) (θ.prod π) :=
    hiF.comp_snd θ
  have hκF : Integrable (fun z => κ z * F z.2) (θ.prod π) := by
    apply hFprod.mono' (hκc.aestronglyMeasurable.mul hFprod.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro z
    simp only [Pi.mul_apply,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hF0 z.2)]
    have hnorm : ‖κ z‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 z)]
      exact hκ1 z
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 z.2),one_mul] using
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg (F z.2))
  have hweight : ∀ᵐ z ∂θ.prod π, Real.exp (w z) ≤ W := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hw.rexp.measurable measurable_const)).mpr
    filter_upwards [sphereLaw_support D.dimension_ge_one] with u hu
    filter_upwards [gibbsLaw_support D.dimension_ge_one β D.baseData.hamiltonian] with x hx
    let Du : SourceData N := {D with
      axis := u,
      axis_onSphere := (onSphere_iff_norm_sq u).mpr hu}
    have hb := PhysicalHitting.regular_source_cutoff_weight_uniform_bound
      Du hJ x ((onSphere_iff_norm_sq x).mpr hx) hβ hh hk hB hR hχB hχR
    dsimp only [w,W]
    rw [D.baseData_hamiltonian]
    simpa only [Du,SourceData.hamiltonian] using hb
  have hewκF : Integrable
      (fun z => Real.exp (w z) * (κ z * F z.2)) (θ.prod π) := by
    apply (hFprod.const_mul W).mono'
      (hw.rexp.aestronglyMeasurable.mul hκF.aestronglyMeasurable)
    filter_upwards [hweight] with z hz
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hκ0 z) (hF0 z.2)))]
    have hle : Real.exp (w z) * κ z ≤ W := by
      calc
        _ ≤ W * κ z := mul_le_mul_of_nonneg_right hz (hκ0 z)
        _ ≤ W * 1 := mul_le_mul_of_nonneg_left (hκ1 z) (Real.exp_nonneg _)
        _ = W := mul_one _
    calc
      Real.exp (w z) * (κ z * F z.2) =
          (Real.exp (w z) * κ z) * F z.2 := by ring
      _ ≤ W * F z.2 := mul_le_mul_of_nonneg_right hle (hF0 z.2)
  have haxisAe : ∀ᵐ x ∂π, (∫ u, κ (u,x) ∂θ) ≤ K := by
    filter_upwards [gibbsLaw_support D.dimension_ge_one β D.baseData.hamiltonian] with x hx
    exact haxis x ((onSphere_iff_norm_sq x).mpr hx)
  have hb := normalizedTilt_killing_mass_le θ π w hw.measurable κ F hiF
    hF0 hκ0 hκF hewκF hK (Real.exp_nonneg _) hM hweight haxisAe
  have hmass : (∫ x, F x ∂π) = 2 := sourceReferencePositivePart_mass_two D β θr hθr
  change (∫ z, κ z * F z.2 ∂normalizedTilt (θ.prod π) w M) ≤ 4 * W * K
  rw [hmass] at hb
  nlinarith [hb]

end SlowEquilibration.ConditionedEntrance
