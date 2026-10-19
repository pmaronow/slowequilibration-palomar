-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureWeightedCap
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt
public import SlowEquilibration.ConditionedEntranceCutoffExponentAbsorption

/-! Exponential cap-killing mass for the actual proper-pure cutoff under
its single normalized axis–Gibbs tilt. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter SphericalModel SphericalForm
open SphericalAging HardSphereDynamics SphericalOverlapExponential
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem pure_cutoff_cap_tail_absorption
    (p : ℕ) (hp : 4 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B β α : ℝ} (hB : 0 ≤ B) (hβ : 0 ≤ β) (hα : 0 < α)
    (hαsmall : α ≤ 1/(128*(1+β*pureCutoffEnergyConstant p (by omega) c hc Q B)))
    (N : ℕ) :
    Real.exp (β*pureCutoffEnergyConstant p (by omega) c hc Q B*(N : ℝ)*α^p)*
      Real.exp (-(N : ℝ)*α^2/64) ≤ Real.exp (-(N : ℝ)*α^2/128) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) c hc
  have hd : μ.minDegree = p := (CSPureModels.pure_degrees p (by omega) c hc).1
  have hμd : 4 ≤ μ.minDegree := by rw [hd]; exact hp
  simpa only [hd] using PhysicalHitting.cutoff_energy_cap_tail_exponent_absorption
    μ hμd hβ (pureCutoffEnergyConstant_nonneg p (by omega) c hc Q B hB)
    hα hαsmall N

/-- Proper-pure cap killing has exponentially small mass under a genuine
probability tilt, uniformly over all good original disorders, smooth
admissible cutoffs and bounded value marks. -/
theorem quenchedPureSource_normalized_capKilling_mean_eventually_le
    (p : ℕ) (hp : 4 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B β α : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale
      (FiniteMixture.pure p (by omega) c hc) Q B (2*β))
    (hαabsorb : α ≤ 1/(128*(1+β*pureCutoffEnergyConstant p (by omega) c hc Q B))) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) c hc
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ J : Disorder (n+1) μ.maxDegree,
        J ∈ EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ →
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e : ℝ), |e| ≤ B →
        let H₀ := fieldOfMixture μ J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β*(pureSourceSmoothCutoffField p (by omega) c hc Q J z.1 e α χ z.2-H₀ z.2)
        let M := ∫ z, Real.exp (w z)
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
        IsProbabilityMeasure
          (normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M) ∧
        (∫ z, PhysicalHitting.capKilling α z.1 z.2
          ∂normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M) ≤
          2*C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) c hc
  have hd : μ.minDegree = p := (CSPureModels.pure_degrees p (by omega) c hc).1
  have hμd : 4 ≤ μ.minDegree := by rw [hd]; exact hp
  obtain ⟨C,hC,hWeighted⟩ :=
    quenchedPureSource_weighted_capKilling_mean_eventually_le p hp c hc hQ hα
  obtain ⟨Cmass,hCmass,hMass⟩ :=
    actual_pureSource_globalTilt_mass_close_one p hp c hc hQ hB hβ
  have hHalf := sourceTilt_eta_eventually_half μ.minDegree hμd Cmass
  refine ⟨C,hC,?_⟩
  filter_upwards [hWeighted,hMass,hHalf] with n hn hm hs
  intro J hJ χ hχ hχb hχR e he
  dsimp only
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β*(pureSourceSmoothCutoffField p (by omega) c hc Q J z.1 e α χ z.2-H₀ z.2)
  let ν := (sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)
  let M := ∫ z, Real.exp (w z) ∂ν
  let κ : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  have hnorm := hm J hJ α hα hαmoment χ hχ hχb hχR e he
  have hMclose : |M-1| ≤ Cmass*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := hnorm.1
  have hprob : IsProbabilityMeasure (normalizedTilt ν w M) := hnorm.2 hs
  have hMhalf : 1/2 ≤ M := by
    have hl := (abs_le.mp hMclose).1
    linarith
  have hMpos : 0 < M := by linarith
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      pureSourceSmoothCutoffField p (by omega) c hc Q J z.1 e α χ z.2) :=
    (pure_axisJointHamiltonian_contDiff p (by omega) c hc Q α χ hχ J e).continuous
  have hw : Measurable w :=
    ((hH.sub ((fieldOfMixture_contDiff μ J).continuous.comp continuous_snd)).const_mul β).measurable
  have hweighted : (∫ z, Real.exp (w z)*κ z ∂ν) ≤
      Real.exp (β*pureCutoffEnergyConstant p (by omega) c hc Q B*
        ((n+1 : ℕ) : ℝ)*α^p)*(C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/64)) :=
    hn J hJ.1 β hβ χ hχ hχb hχR B e hB he
  have habsorb := pure_cutoff_cap_tail_absorption p hp c hc hB hβ hα hαabsorb (n+1)
  have hnum : (∫ z, Real.exp (w z)*κ z ∂ν) ≤
      C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128) := by
    calc
      _ ≤ Real.exp (β*pureCutoffEnergyConstant p (by omega) c hc Q B*
          ((n+1 : ℕ) : ℝ)*α^p)*(C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/64)) := hweighted
      _ = C*(Real.exp (β*pureCutoffEnergyConstant p (by omega) c hc Q B*
          ((n+1 : ℕ) : ℝ)*α^p)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/64)) := by ring
      _ ≤ C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128) :=
        mul_le_mul_of_nonneg_left habsorb hC.le
  refine ⟨hprob,?_⟩
  change (∫ z, κ z ∂normalizedTilt ν w M) ≤ _
  rw [integral_normalizedTilt ν w hw hMpos]
  apply (div_le_iff₀ hMpos).2
  have hmprod := mul_le_mul_of_nonneg_left hMhalf (show 0 ≤
    2*(C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128)) by positivity)
  nlinarith only [hnum,hmprod]

end SlowEquilibration.ConditionedEntrance
