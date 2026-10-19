-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelBandSecondMoment
public import SlowEquilibration.SourcePureCapBorelBandSquareIntegrable
public import SlowEquilibration.SphericalTAPPurePalmDeterminantQuadraticReduction

/-! The arbitrary-Borel pure cap band has a determinant-weighted Palm
expectation bounded by its exact original posterior mean. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelDeterminantPalm
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open PureStationarity ConditionedDeterminantMoments
open SourcePureCapBorelBandSecondMoment
open SourcePureCapBorelBandSquareIntegrable
open SphericalTAPPurePalmDeterminantQuadraticReduction
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_borel_band_determinant_palm_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2)
    {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2 : ℕ) : ℝ))
        (H : ℝ),
        2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*(H/(d+2:ℕ)) →
        ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Ico a 1 →
        let c := centerCoefficients (mixtureCoefficients μ) 1
        let ν := valueConditionedLaw c u hu (H/(d+2:ℕ))
        let Z := fun J => partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I)
        let D := intrinsicDet μ 1 u
        Integrable (fun J => D J*Z J) ν ∧
          (∫ J, D J*Z J ∂ν) ≤ C*(∫ J, D J ∂ν)*(∫ J, Z J ∂ν) := by
  dsimp only
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  obtain ⟨C₂,hC₂,hMoment⟩ := pure_original_conditioned_borel_band_second_moment
    p hp β ha hsub
  let K : ℝ := (2:ℝ)^2 * Real.exp (4*(μ.xi2 1)*(2:ℝ)^2/g^2)
  let C : ℝ := Real.sqrt K*Real.sqrt C₂
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := mul_pos (Real.sqrt_pos.mpr hK) (Real.sqrt_pos.mpr hC₂)
  have hDet := pure_determinant_quadratic_bank_cauchy_eventually
    p hp 1 (by positivity) (Q := 1) (by positivity) hg
  obtain ⟨n₀,hn₀⟩ := Filter.eventually_atTop.1 hMoment
  refine ⟨C,hC,?_⟩
  filter_upwards [hDet,Filter.eventually_ge_atTop n₀] with d hd hdn
  intro u hu H hEdge I hI hIcap
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let ν := valueConditionedLaw c u hu (H/(d+2:ℕ))
  let Z : Disorder (d+2) μ.maxDegree → ℝ := fun J =>
    partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I)
  let D : Disorder (d+2) μ.maxDegree → ℝ := intrinsicDet μ 1 u
  let m : ℝ := ∫ J, Z J ∂ν
  have hZ₀ : ∀ J, 0 ≤ Z J := by
    intro J
    dsimp [Z]
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hm : 0 ≤ m := integral_nonneg hZ₀
  have hZmeas : Measurable Z := by
    have hComp : Measurable (fun J : Disorder (d+2) μ.maxDegree => (J,u)) := by
      fun_prop
    have h := (overlapRestrictedPartition_measurable (N := d+2)
      (mixtureCoefficients μ) β hI).comp hComp
    simpa only [Z,overlapRestrictedPartition,overlapRegion,Function.comp_def] using h
  have hSq : Integrable (fun J => (Z J)^2) ν := by
    simpa only [Z,ν,c,μ,show d+1+1=d+2 by omega] using
      pure_original_conditioned_borel_band_square_integrable
        (d+1) p hp u (by simpa only [show d+1+1=d+2 by omega] using hu)
        β H hI
  have hMoment' : (∫ J, (Z J)^2 ∂ν) ≤ C₂*m^2 := by
    have hh := hn₀ (d+1) (by omega) u
      (by simpa only [show d+1+1=d+2 by omega] using hu) H I hI hIcap
    simpa only [Z,ν,c,m,μ,show d+1+1=d+2 by omega] using hh
  have hLaw : pureLaw p hp 1 (by positivity) 1 u hu (H/(d+2:ℕ)) = ν :=
    pureLaw_eq_valueConditionedLaw p hp 1 (by positivity)
      1 u hu (H/(d+2:ℕ))
  have hDet' := hd u hu (H/(d+2:ℕ)) (by
      simpa only [μ,one_pow,one_mul] using hEdge)
    Z (m := 1) (C := C₂*m^2) (by norm_num) hZ₀ hZmeas
    (by simpa only [div_one,hLaw] using hSq)
    (by simpa only [div_one,hLaw] using hMoment')
  dsimp only at hDet'
  rw [hLaw] at hDet'
  have hSqrt : Real.sqrt (C₂*m^2) = Real.sqrt C₂*m := by
    rw [Real.sqrt_mul hC₂.le,Real.sqrt_sq_eq_abs,abs_of_nonneg hm]
  constructor
  · simpa only [D,Z,ν,c,μ] using hDet'.1
  · have hbound := hDet'.2
    rw [hSqrt] at hbound
    have hKsame : (2:ℝ)^2*Real.exp
        (4*(1^2*μ.xi2 1)*(2:ℝ)^2/g^2) = K := by
      simp only [one_pow,one_mul]
      rfl
    rw [hKsame] at hbound
    convert hbound using 1; ring

end
end SlowEquilibration.SourcePureCapBorelDeterminantPalm
