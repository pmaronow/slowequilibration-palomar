-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureDenominatorScaleComparison
public import SlowEquilibration.SphericalPureCapOriginalMeanDepth

/-! The pure denominator lower tail at the original posterior cap mean. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorOriginal
noncomputable section
open Filter Set MeasureTheory SphericalModel SphericalTAPCertificate
open SphericalMarkedWindows SphericalGaussianJet
open SphericalPureCapOriginalMeanDepth SphericalPureDenominatorScaleComparison
open SphericalPureCapIntegralDecomposition SphericalPureCapSourceScalars
open PureStationarity
open scoped Topology
set_option autoImplicit false

/-- Source `pc-denominator` with `𝒜_N` defined as the original value-conditioned
mean of the partition function of the half-open cap `[a,1)`. The pole can be
any deterministic point on the sphere in each dimension. -/
theorem pure_original_partition_conditioned_cap_denominator_lower_tail
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (u : ∀ n : ℕ, Vector (n+3))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+3:ℕ)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a : ℝ, 1/Real.sqrt 2 < a ∧ a < Real.sqrt Q ∧
      pureResidualCoefficient p β a < 1/2 ∧ cp < β*a^p ∧
      ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
        Filter.limsup (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
              η*(∫ J', partitionOn β (field (mixtureCoefficients μ) J')
                (overlapRegion (u n) (Ico a 1))
                ∂valueConditionedLaw c (u n) (hu n)
                  (s*(((n+3:ℕ):ℝ)*ep-
                    Real.log (n+3:ℕ)/(2*cp))/(n+3:ℕ)))}) atTop ≤ ε := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  obtain ⟨a,ha,haQ,hres,hdepth,hTail⟩ :=
    pure_original_partition_raw_cap_denominator_lower_tail p hp h
  have ha0 : 0 < a := lt_trans (by positivity : (0:ℝ) < 1/Real.sqrt 2) ha
  have ha1 : a < 1 := by
    have hq1 : Real.sqrt Q < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
    simpa only [Real.sqrt_one] using lt_trans haQ hq1
  have hEq (n : ℕ) (hn : 1 ≤ n) :
      (∫ J', partitionOn β (field (mixtureCoefficients μ) J')
        (overlapRegion (u n) (Ico a 1))
        ∂valueConditionedLaw c (u n) (hu n)
          (s*(((n+3:ℕ):ℝ)*ep-
            Real.log (n+3:ℕ)/(2*cp))/(n+3:ℕ))) =
      (latitudeNormalization (n+2)).toReal *
        (∫ z in a..1, rawDensity p (n+3) β
          (((n+3:ℕ):ℝ)*ep-Real.log (n+3:ℕ)/(2*cp)) z) := by
    have hnorm : ‖u n‖^2=(n+2+1:ℕ) := by
      simpa only [Nat.add_assoc,Nat.reduceAdd] using hu n
    have hh := pure_original_conditioned_cap_mean_raw
      (n+2) p (by omega) hp h.overlap_range.1 (u n) hnorm β
      (((n+3:ℕ):ℝ)*ep-Real.log (n+3:ℕ)/(2*cp)) a ha0 ha1
    simpa only [μ,c,s,cp,ep,Nat.add_assoc,Nat.reduceAdd] using hh
  refine ⟨a,ha,haQ,hres,hdepth,?_⟩
  intro ε hε
  obtain ⟨η,hη,hBound⟩ := hTail ε hε
  refine ⟨η,hη,?_⟩
  have hEventEq :
      (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
            η*(∫ J', partitionOn β (field (mixtureCoefficients μ) J')
              (overlapRegion (u n) (Ico a 1))
              ∂valueConditionedLaw c (u n) (hu n)
                (s*(((n+3:ℕ):ℝ)*ep-
                  Real.log (n+3:ℕ)/(2*cp))/(n+3:ℕ)))}) =ᶠ[atTop]
      (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
            η*((latitudeNormalization (n+2)).toReal *
              (∫ z in a..1, rawDensity p (n+3) β
                (((n+3:ℕ):ℝ)*ep-Real.log (n+3:ℕ)/(2*cp)) z))}) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hEq n hn]
  have hLim := limsup_congr hEventEq
  simpa only [μ,c,s,cp,ep] using hLim.le.trans hBound

/-- The literal right-hand limit in source `pc-denominator` for the original
pure-model conditional cap mean. -/
theorem pure_original_partition_conditioned_cap_denominator_limit
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (u : ∀ n : ℕ, Vector (n+3))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+3:ℕ)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a : ℝ, 1/Real.sqrt 2 < a ∧ a < Real.sqrt Q ∧
      pureResidualCoefficient p β a < 1/2 ∧ cp < β*a^p ∧
      Tendsto (fun η : ℝ => Filter.limsup (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
            η*(∫ J', partitionOn β (field (mixtureCoefficients μ) J')
              (overlapRegion (u n) (Ico a 1))
              ∂valueConditionedLaw c (u n) (hu n)
                (s*(((n+3:ℕ):ℝ)*ep-
                  Real.log (n+3:ℕ)/(2*cp))/(n+3:ℕ)))}) atTop)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  obtain ⟨a,ha,haQ,hres,hdepth,hTail⟩ :=
    pure_original_partition_conditioned_cap_denominator_lower_tail p hp h u hu
  let A (n : ℕ) :=
    (∫ J', partitionOn β (field (mixtureCoefficients μ) J')
      (overlapRegion (u n) (Ico a 1))
      ∂valueConditionedLaw c (u n) (hu n)
        (s*(((n+3:ℕ):ℝ)*ep-Real.log (n+3:ℕ)/(2*cp))/(n+3:ℕ)))
  let P (η : ℝ) (n : ℕ) :=
    (disorderLaw (n+3) μ.maxDegree).real
      {J | partition (n+3) β (field (mixtureCoefficients μ) J) < η*A n}
  let f (η : ℝ) := Filter.limsup (P η) atTop
  have hA (n : ℕ) : 0 ≤ A n := by
    dsimp only [A]
    exact integral_nonneg (fun J' => partitionOn_nonneg β _ _)
  have hPnonneg (η : ℝ) (n : ℕ) : 0 ≤ P η n := measureReal_nonneg
  have hPbounded (η : ℝ) : IsBoundedUnder (· ≤ ·) atTop (P η) :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hPcobounded (η : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (P η) :=
    isCoboundedUnder_le_of_le atTop (fun n => hPnonneg η n)
  have hf_nonneg (η : ℝ) : 0 ≤ f η := by
    have hZeroCob : IsCoboundedUnder (· ≤ ·) atTop
        (fun _ : ℕ => (0:ℝ)) :=
      isCoboundedUnder_le_of_le atTop (fun _ => le_refl 0)
    have hh := limsup_le_limsup
      (Filter.Eventually.of_forall (fun n => hPnonneg η n))
      hZeroCob (hPbounded η)
    simpa only [f,limsup_const] using hh
  have hf_mono {η₁ η₂ : ℝ} (hη : η₁ ≤ η₂) : f η₁ ≤ f η₂ := by
    apply limsup_le_limsup (h := ?_) (hPcobounded η₁) (hPbounded η₂)
    exact Filter.Eventually.of_forall (fun n =>
      measureReal_mono
        (fun J hJ => lt_of_lt_of_le hJ (mul_le_mul_of_nonneg_right hη (hA n)))
        (by finiteness))
  have hf_small (ε : ℝ) (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ f η ≤ ε := by
    obtain ⟨η,hη,hBound⟩ := hTail ε hε
    exact ⟨η,hη,by simpa only [f,P,A,μ,c,s,cp,ep] using hBound⟩
  refine ⟨a,ha,haQ,hres,hdepth,?_⟩
  change Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0)
  refine tendsto_order.mpr ⟨?_,?_⟩
  · intro z hz
    filter_upwards with η
    exact hz.trans_le (hf_nonneg η)
  · intro z hz
    obtain ⟨η₀,hη₀,hupper⟩ := hf_small (z/2) (half_pos hz)
    filter_upwards [Ioc_mem_nhdsGT hη₀] with η hη
    exact (hf_mono hη.2).trans_lt (lt_of_le_of_lt hupper (by linarith))

end
end SlowEquilibration.SphericalPureDenominatorOriginal
