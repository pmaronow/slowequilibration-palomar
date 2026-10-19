-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureReferenceMassTwo
public import SlowEquilibration.ConditionedEntranceNormalizedHazardMass
public import SlowEquilibration.ConditionedEntrancePureWeightedCap
public import SlowEquilibration.ConditionedEntranceSourceJointKilling

/-! Genuine original-reference cap hazard for the proper-pure global tilt. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral
open SphericalAging HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pureReference_normalized_capKilling_le
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B α : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hα : 0 < α)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχB : ∀ s, |χ s| ≤ 1) (hχR : ∀ s, 2 < |s| → χ s = 0)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (e : ℝ) (he : |e| ≤ B)
    (β : ℝ) (hβ : 0 ≤ β) (θr : ℝ≥0) (hθr : 0 < θr)
    {K : ℝ} (hK : 0 ≤ K)
    (haxis : ∀ x : Vector (n+1), OnSphere x →
      (∫ u, PhysicalHitting.capKilling α u x ∂sphereLaw (n+1)) ≤ K) :
    let D₀ := FieldData.ofOriginal (by omega : 1 ≤ n+1) (FiniteMixture.pure p hp c hc) J
    let π := gibbsLaw (n+1) β D₀.hamiltonian
    let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
      β*(pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2-D₀.hamiltonian z.2)
    let M := ∫ z, Real.exp (w z) ∂((sphereLaw (n+1)).prod π)
    1/2 ≤ M →
    (∫ z, PhysicalHitting.capKilling α z.1 z.2*fieldReferencePositivePart D₀ β θr z.2
      ∂normalizedTilt ((sphereLaw (n+1)).prod π) w M) ≤
      4*Real.exp (β*pureCutoffEnergyConstant p hp c hc Q B*((n+1 : ℕ) : ℝ)*α^p)*K := by
  dsimp only
  have hN : 1 ≤ n+1 := by omega
  let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure p hp c hc) J
  let π := gibbsLaw (n+1) β D₀.hamiltonian
  let θ := sphereLaw (n+1)
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2 -
        D₀.hamiltonian z.2)
  let κ : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  let F : Vector (n+1) → ℝ := fieldReferencePositivePart D₀ β θr
  let W := Real.exp (β*pureCutoffEnergyConstant p hp c hc Q B*((n+1 : ℕ) : ℝ)*α^p)
  let M := ∫ z, Real.exp (w z) ∂θ.prod π
  intro hM
  let : IsProbabilityMeasure θ := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β
    D₀.hamiltonian_contDiff.continuous
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2) :=
    (pure_axisJointHamiltonian_contDiff p hp c hc Q α χ hχ J e).continuous
  have hw : Continuous w :=
    (hH.sub (D₀.hamiltonian_contDiff.continuous.comp continuous_snd)).const_mul β
  have hκc : Continuous κ := capKilling_jointContinuous α
  have hκ0 (z : Vector (n+1) × Vector (n+1)) : 0 ≤ κ z :=
    PhysicalHitting.capKilling_nonneg α z.1 z.2
  have hκ1 (z : Vector (n+1) × Vector (n+1)) : κ z ≤ 1 :=
    PhysicalHitting.capKilling_le_one hα z.1 z.2
  have hF0 (x : Vector (n+1)) : 0 ≤ F x := le_max_left _ _
  have hiF : Integrable F π := fieldReferencePositivePart_integrable D₀ β θr
  have hFprod : Integrable (fun z : Vector (n+1) × Vector (n+1) => F z.2) (θ.prod π) :=
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
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [gibbsLaw_support hN β D₀.hamiltonian] with x hx
    have hb := regular_pure_source_cutoff_energy_difference n p hp c hc hQ hB hα J hJ
      u x ((onSphere_iff_norm_sq u).mpr hu) ((onSphere_iff_norm_sq x).mpr hx)
      e he χ hχB hχR
    apply Real.exp_le_exp.mpr
    dsimp only [w,W,D₀,FieldData.ofOriginal_hamiltonian]
    apply (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hβ).trans_eq
    dsimp only [pureCutoffEnergyConstant]
    ring
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
    filter_upwards [gibbsLaw_support hN β D₀.hamiltonian] with x hx
    exact haxis x ((onSphere_iff_norm_sq x).mpr hx)
  have hb := normalizedTilt_killing_mass_le θ π w hw.measurable κ F hiF
    hF0 hκ0 hκF hewκF hK (Real.exp_nonneg _) hM hweight haxisAe
  have hmass : (∫ x, F x ∂π) = 2 := fieldReferencePositivePart_mass_two D₀ β θr hθr
  change (∫ z, κ z * F z.2 ∂normalizedTilt (θ.prod π) w M) ≤ 4 * W * K
  rw [hmass] at hb
  nlinarith [hb]



end SlowEquilibration.ConditionedEntrance
