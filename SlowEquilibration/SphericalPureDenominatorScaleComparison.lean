-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureDenominatorScaleLower
public import SlowEquilibration.SphericalPureCapFullLaplaceUniform
public import SlowEquilibration.SphericalTAPCriticalPureBandScaleAsymptotic

/-! Compare the selected critical-band scale with the manuscript's
logarithmically centered annealed latitude integral. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorScaleComparison
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalModel SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalPureBandScaleIdentity
open SphericalTAPCriticalPureBandScaleAsymptotic
open SphericalPureCapTailScale SphericalPureCapFullLaplace
open SphericalPureCapFullLaplaceUniform SphericalPureCapIntegralDecomposition
open SphericalPureCapSourceScalars
open PureStationarity
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Exact algebra: after removing the contact exponential and polynomial,
the source band scale differs from the coarea factor only by the bounded
centering error. The center is measured in the physical H_Q energy. -/
theorem pure_band_scale_cap_normalization_exact
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (n : ℕ) (m : ℕ → ℝ) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let F := CSParisiMeasure.variationalValue μ β
    let N : ℝ := (n+3:ℕ)
    capScale (n+3) F (1/(2*x)) *
      sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1)) =
      (1-Q)^(-(3/2:ℝ)) *
        ((latitudeNormalization (n+2)).toReal / Real.sqrt N) *
        Real.exp (β*(m (n+1)-(N*E-Real.log N/(2*(β*x))))) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let F := CSParisiMeasure.variationalValue μ β
  let N : ℝ := (n+3:ℕ)
  let R : ℝ := (1-Q)^(-(3/2:ℝ)) *
    ((latitudeNormalization (n+2)).toReal / Real.sqrt N)
  have hN : 0 < N := by dsimp [N]; positivity
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hx : 0 < x := h.weight_range.1
  have hm : N*(m (n+1)/N)=m (n+1) := by field_simp
  have hIdentity := sourcePure_bandScale_exact_identity p (by omega) 1
    (by positivity) h (n+2) (by omega)
      (m (n+1)/N) (m (n+1))
  have hD : sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1)) =
      R*Real.exp (N*F+β*(m (n+1)-N*E)) := by
    dsimp only at hIdentity
    rw [hm,sub_self,mul_zero,Real.exp_zero,mul_one] at hIdentity
    calc
      _ = R*Real.exp (N*(F+β*(m (n+1)/N-E))) := by
        simpa only [R,N,F,E,μ,Nat.add_assoc,Nat.reduceAdd] using hIdentity
      _ = _ := by
        congr 1
        field_simp
  calc
    capScale (n+3) F (1/(2*x)) *
        sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1)) =
      ((N:ℝ)^(1/(2*x))*Real.exp (-N*F)) *
        (R*Real.exp (N*F+β*(m (n+1)-N*E))) := by
          rw [hD]
          rfl
    _ = R*(N^(1/(2*x))*Real.exp (β*(m (n+1)-N*E))) := by
      calc
        _ = R*(N^(1/(2*x))*(Real.exp (-N*F)*
          Real.exp (N*F+β*(m (n+1)-N*E)))) := by ring
        _ = _ := by
          rw [←Real.exp_add]
          rw [show -N*F+(N*F+β*(m (n+1)-N*E)) =
            β*(m (n+1)-N*E) by ring]
    _ = R*Real.exp ((1/(2*x))*Real.log N+β*(m (n+1)-N*E)) := by
      rw [Real.rpow_def_of_pos hN,←Real.exp_add]
      congr 1
      ring
    _ = R*Real.exp (β*(m (n+1)-(N*E-Real.log N/(2*(β*x))))) := by
      congr 1
      have hβ : β ≠ 0 := h.beta_pos.ne'
      have hx0 : x ≠ 0 := hx.ne'
      field_simp
      ring

/-- Every logarithmically centered pure critical-band scale is bounded
below at the manuscript's annealed cap normalization, uniformly for all
large dimensions. -/
theorem pure_centered_band_scale_normalized_eventually_lower
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (m : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-((j+2:ℕ)*markE
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q-
        Real.log (j+2:ℕ)/(2*(β*x)))| ≤ M) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let F := CSParisiMeasure.variationalValue μ β
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop,
      d ≤ capScale (n+3) F (1/(2*x)) *
        sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let F := CSParisiMeasure.variationalValue μ β
  let r0 := (1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)
  let R (n : ℕ) := (1-Q)^(-(3/2:ℝ)) *
    ((latitudeNormalization (n+2)).toReal /
      Real.sqrt (((n+3:ℕ):ℝ)))
  let z (n : ℕ) := m (n+1)-
    (((n+3:ℕ):ℝ)*E-Real.log (n+3:ℕ)/(2*(β*x)))
  have hs : 0 < 1-Q := sub_pos.mpr h.overlap_range.2
  have hr0 : 0 < r0 := div_pos (Real.rpow_pos_of_pos hs _)
    (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
  have hR : Tendsto R atTop (𝓝 r0) := by
    have hh := SphericalModel.latitudeNormalization_toReal_div_sqrt_tendsto.comp
      (tendsto_add_atTop_nat 2)
    have ht := hh.const_mul ((1-Q)^(-(3/2:ℝ)))
    simpa only [R,r0,mul_one_div,Function.comp_def,Nat.add_assoc,Nat.reduceAdd]
      using ht
  have hRLower : ∀ᶠ n : ℕ in atTop, r0/2 ≤ R n := by
    filter_upwards [hR.eventually
      (lt_mem_nhds (show r0/2 < r0 by linarith))] with n hn
    exact hn.le
  have hz : ∀ᶠ n : ℕ in atTop, -M ≤ z n := by
    have hh := (tendsto_add_atTop_nat 1).eventually hcenter
    filter_upwards [hh] with n hn
    exact (abs_le.mp hn).1
  have hβ : 0 < β := h.beta_pos
  let d := (r0/2)*Real.exp (-β*M)
  have hd : 0 < d := mul_pos (half_pos hr0) (Real.exp_pos _)
  refine ⟨d,hd,?_⟩
  filter_upwards [hRLower,hz] with n hnR hnz
  have hexp : Real.exp (-β*M) ≤ Real.exp (β*z n) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hnz hβ.le])
  have hRnonneg : 0 ≤ R n := (by positivity : 0 ≤ r0/2).trans hnR
  have hscale := pure_band_scale_cap_normalization_exact p hp h n m
  change capScale (n+3) F (1/(2*x)) *
      sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1)) =
        R n*Real.exp (β*z n) at hscale
  rw [hscale]
  calc
    d = (r0/2)*Real.exp (-β*M) := rfl
    _ ≤ R n*Real.exp (-β*M) :=
      mul_le_mul_of_nonneg_right hnR (Real.exp_pos _).le
    _ ≤ R n*Real.exp (β*z n) :=
      mul_le_mul_of_nonneg_left hexp hRnonneg

/-- Any cap quantity with a finite limit at the printed annealed scale is
eventually bounded by a fixed multiple of the source critical-band scale,
for every selected center with the proved logarithmic error bound. -/
theorem pure_cap_quantity_eventually_le_band_scale
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (m : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-((j+2:ℕ)*markE
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q-
        Real.log (j+2:ℕ)/(2*(β*x)))| ≤ M)
    (A : ℕ → ℝ) (K : ℝ)
    (hA : Tendsto (fun n : ℕ => capScale (n+3)
      (CSParisiMeasure.variationalValue
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
      (1/(2*x))*A n) atTop (𝓝 K)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      A n ≤ C*sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨d,hd,hD⟩ := pure_centered_band_scale_normalized_eventually_lower
    p hp h m M hM hcenter
  let B := |K|+1
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg K]
  have hKB : K < B := by dsimp [B]; linarith [le_abs_self K]
  have hAUpper : ∀ᶠ n : ℕ in atTop,
      capScale (n+3) F (1/(2*x))*A n ≤ B := by
    filter_upwards [hA.eventually (gt_mem_nhds hKB)] with n hn
    exact hn.le
  let C := B/d
  have hC : 0 < C := div_pos hB hd
  refine ⟨C,hC,?_⟩
  filter_upwards [hAUpper,hD] with n hnA hnD
  have hcap : 0 < capScale (n+3) F (1/(2*x)) := by
    unfold capScale
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  have hprod : capScale (n+3) F (1/(2*x))*A n ≤
      capScale (n+3) F (1/(2*x)) *
        (C*sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1))) := by
    calc
      _ ≤ B := hnA
      _ = C*d := by dsimp [C]; field_simp
      _ ≤ C*(capScale (n+3) F (1/(2*x)) *
          sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1))) :=
        mul_le_mul_of_nonneg_left hnD hC.le
      _ = _ := by ring
  exact le_of_mul_le_mul_left hprod hcap

/-- The full source pure-cap Laplace theorem gives the exact deterministic
comparison needed to pass a denominator lower bound from the Palm scale to
the manuscript's unnormalized annealed cap mean. -/
theorem pure_source_cap_mean_eventually_le_band_scale
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (m : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-((j+2:ℕ)*markE
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q-
        Real.log (j+2:ℕ)/(2*(β*x)))| ≤ M) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a C : ℝ, 1/Real.sqrt 2 < a ∧ a < Real.sqrt Q ∧
      pureResidualCoefficient p β a < 1/2 ∧ cp < β*a^p ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (latitudeNormalization (n+2)).toReal *
          (∫ z in a..1, rawDensity p (n+3) β
            ((n+3:ℕ)*ep-Real.log (n+3:ℕ)/(2*cp)) z) ≤
        C*sourceCriticalBandScale (n+2) μ h.overlap_range β
          (m (n+1)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hUniform⟩ :=
    sourcePure_cap_full_laplace_uniform p hp h 0 (by norm_num)
  let A (n : ℕ) := (latitudeNormalization (n+2)).toReal *
    (∫ z in a..1, rawDensity p (n+3) β
      ((n+3:ℕ)*ep-Real.log (n+3:ℕ)/(2*cp)) z)
  let K := ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
    Real.sqrt (Real.pi/(κ/2))
  have hA : Tendsto (fun n : ℕ => capScale (n+3) F (1/(2*x))*A n)
      atTop (𝓝 K) := by
    have h0 := hUniform.tendsto_at
      (show (0:ℝ) ∈ Icc (-(0:ℝ)) 0 by simp)
    have h1 := h0.comp (tendsto_add_atTop_nat 1)
    simpa only [A,K,F,cp,ep,Function.comp_def,Nat.add_assoc,Nat.reduceAdd,
      mul_zero,zero_mul,add_zero,Real.exp_zero,mul_one] using h1
  obtain ⟨C,hC,hBound⟩ := pure_cap_quantity_eventually_le_band_scale
    p hp h m M hM hcenter A K hA
  exact ⟨a,C,ha,by linarith [hab,hb],hres,hdepth,hC,
    by simpa only [A,μ,cp,ep] using hBound⟩

/-- Unconditional source `pc-denominator` lower-tail statement for the
literal raw annealed full-cap quantity. The cap is fixed once from the
certificate, before the target probability and dimension. -/
theorem pure_original_partition_raw_cap_denominator_lower_tail
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a : ℝ, 1/Real.sqrt 2 < a ∧ a < Real.sqrt Q ∧
      pureResidualCoefficient p β a < 1/2 ∧ cp < β*a^p ∧
      ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
        Filter.limsup (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
              η*((latitudeNormalization (n+2)).toReal *
                (∫ z in a..1, rawDensity p (n+3) β
                  ((n+3:ℕ)*ep-Real.log (n+3:ℕ)/(2*cp)) z))}) atTop ≤ ε := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  obtain ⟨m,M,hM,hcenter,hScale⟩ :=
    SphericalPureDenominatorScaleLower.pure_partition_source_band_scale_lower_tail
      p (by omega) 1 (by positivity) h
  obtain ⟨a,C,ha,haQ,hres,hdepth,hC,hComp⟩ :=
    pure_source_cap_mean_eventually_le_band_scale p hp h m M hM.le hcenter
  let A (n : ℕ) := (latitudeNormalization (n+2)).toReal *
    (∫ z in a..1, rawDensity p (n+3) β
      ((n+3:ℕ)*ep-Real.log (n+3:ℕ)/(2*cp)) z)
  refine ⟨a,ha,haQ,hres,hdepth,?_⟩
  intro ε hε
  let ρ := ε/2
  have hρ : 0 < ρ := half_pos hε
  obtain ⟨L,δ,b,hL,hδ,hb,hLow⟩ := hScale ρ hρ
  let η := δ*Real.exp (-β*L)/C
  have hη : 0 < η := div_pos (mul_pos hδ (Real.exp_pos _)) hC
  refine ⟨η,hη,?_⟩
  let low (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | partition (n+3) β (field (mixtureCoefficients μ) J) < η*A n}
  let sourceLow (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
      δ*Real.exp (-β*L)*sourceCriticalBandScale (n+2) μ h.overlap_range β
        (m (n+1))}
  have hEventual : ∀ᶠ n : ℕ in atTop, low n ≤ sourceLow n := by
    filter_upwards [hComp] with n hn
    have hthreshold : η*A n ≤
        δ*Real.exp (-β*L)*sourceCriticalBandScale (n+2) μ
          h.overlap_range β (m (n+1)) := by
      calc
        _ ≤ η*(C*sourceCriticalBandScale (n+2) μ
            h.overlap_range β (m (n+1))) :=
          mul_le_mul_of_nonneg_left hn hη.le
        _ = _ := by
          dsimp [η]
          field_simp
    exact measureReal_mono (fun J hJ => lt_of_lt_of_le hJ hthreshold)
      (by finiteness)
  have hLowCob : IsCoboundedUnder (· ≤ ·) atTop low :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  have hSourceB : IsBoundedUnder (· ≤ ·) atTop sourceLow :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hh := limsup_le_limsup hEventual hLowCob hSourceB
  have hfinal := hh.trans hLow
  simpa only [low,sourceLow,A,ρ,show 2*(ε/2)=ε by ring,μ,cp,ep]
    using hfinal

end
end SlowEquilibration.SphericalPureDenominatorScaleComparison
