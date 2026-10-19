-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapFullLaplace
public import SlowEquilibration.SourceUniformMonotoneParameter

@[expose] public section

/-! Uniformity in the source energy shift of the complete pure cap Laplace
limit. Positivity of the raw cap integrand makes the finite-dimensional
quantity monotone in the shift, so the pointwise limit upgrades uniformly
on any compact shift interval. -/

namespace SlowEquilibration.SphericalPureCapFullLaplaceUniform
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalPureCapIntegralDecomposition SphericalPureCapTailScale
open SphericalPureCapSourceScalars
open SphericalPureCapFullLaplace SourceUniformMonotoneParameter
open SphericalPureLaplaceUniformLogCurvature PureStationarity SphericalModel
open scoped Topology
set_option autoImplicit false

/-- The original entropy-power cap integral increases with its critical
value, including the endpoint at the pole. -/
theorem raw_cap_integral_monotone_energy (p N : ℕ) (hN : 4 ≤ N)
    {β a : ℝ} (hβ : 0 < β) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Monotone (fun H : ℝ => ∫ z in a..1, rawDensity p N β H z) := by
  have hpow : 0 ≤ ((N:ℝ)-3)/2 := by
    have hNr : (4:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpowCont : Continuous (fun z : ℝ => (1-z^2)^(((N:ℝ)-3)/2)) :=
    (Real.continuous_rpow_const hpow).comp
      (continuous_const.sub (continuous_id.pow 2))
  have hresCont : Continuous (pureResidualCoefficient p β) := by
    unfold pureResidualCoefficient pureResidualAtOne
    fun_prop
  have hi (H : ℝ) : IntervalIntegrable (rawDensity p N β H) volume a 1 := by
    apply Continuous.intervalIntegrable
    unfold rawDensity
    exact hpowCont.mul (Real.continuous_exp.comp (by fun_prop))
  intro H₁ H₂ hH
  apply intervalIntegral.integral_mono_on ha1.le (hi H₁) (hi H₂)
  intro z hz
  have hz0 : 0 ≤ z := ha0.trans hz.1
  have hz1 : z ≤ 1 := hz.2
  have hzpow : 0 ≤ z^p := pow_nonneg hz0 _
  have hβpow : 0 ≤ β*z^p := mul_nonneg hβ.le hzpow
  have harg : β*H₁*z^p+(N:ℝ)*pureResidualCoefficient p β z/2 ≤
      β*H₂*z^p+(N:ℝ)*pureResidualCoefficient p β z/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hH hβpow]
  have hbase : 0 ≤ 1-z^2 := by nlinarith [hz0,hz1]
  have hfac : 0 ≤ (1-z^2)^(((N:ℝ)-3)/2) := Real.rpow_nonneg hbase _
  unfold rawDensity
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hfac

/-- The complete source pure cap Gaussian limit is uniform over bounded
critical-value shifts. The geometric cap and contact band are chosen once
for the entire interval. -/
theorem sourcePure_cap_full_laplace_uniform
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (L : ℝ) (hL : 0 ≤ L) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    let F := CSParisiMeasure.variationalValue μ β
    ∃ a b ε κ : ℝ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ q+b < 1-ε ∧
      0 < ε ∧ ε < 1 ∧ 0 < κ ∧
      κ = purePrintedKStar p hp β Q ∧
      pureResidualCoefficient p β a < 1/2 ∧
      cp < β*a^p ∧
      TendstoUniformlyOn
        (fun n : ℕ => fun t : ℝ =>
          capScale (n+2) F (1/(2*x)) *
            ((latitudeNormalization (n+1)).toReal *
              (∫ z in a..1,
                rawDensity p (n+2) β
                  ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z)))
        (fun t : ℝ =>
          ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
            Real.exp (β*t*q^p) * Real.sqrt (Real.pi/(κ/2)))
        atTop (Icc (-L) L) := by
  dsimp only
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hpoint⟩ :=
    sourcePure_cap_full_laplace_pointwise p hp h L hL
  refine ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,?_⟩
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let F := CSParisiMeasure.variationalValue μ β
  let G : ℕ → ℝ → ℝ := fun n t =>
    capScale (n+2) F (1/(2*x)) *
      ((latitudeNormalization (n+1)).toReal *
        (∫ z in a..1, rawDensity p (n+2) β
          ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z))
  let clamp : ℝ → ℝ := fun t => max (-L) (min L t)
  have hclampMono : Monotone clamp := by
    intro s t hst
    exact max_le_max le_rfl (min_le_min le_rfl hst)
  have hclampMem (t : ℝ) : clamp t ∈ Icc (-L) L := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hclampEq (t : ℝ) (ht : t ∈ Icc (-L) L) : clamp t = t := by
    simp [clamp, min_eq_right ht.2, max_eq_right ht.1]
  let G' : ℕ → ℝ → ℝ := fun n t => if n ≤ 1 then 0 else G n (clamp t)
  let g : ℝ → ℝ := fun t =>
    ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
      Real.exp (β*t*q^p) * Real.sqrt (Real.pi/(κ/2))
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hmono : ∀ n, Monotone (G' n) := by
    intro n
    by_cases hn : n ≤ 1
    · simpa only [G', hn, ↓reduceIte] using
        (monotone_const : Monotone (fun _ : ℝ => (0:ℝ)))
    · have hN : 4 ≤ n+2 := by omega
      have ha0 : 0 ≤ a := (by positivity : 0 < 1/Real.sqrt 2).trans ha |>.le
      have ha1 : a < 1 := by
        have hq1 : q < 1 := by linarith
        linarith
      intro t₁ t₂ ht
      have hH : (n+2:ℝ)*ep+clamp t₁-Real.log (n+2:ℝ)/(2*cp) ≤
          (n+2:ℝ)*ep+clamp t₂-Real.log (n+2:ℝ)/(2*cp) := by
        linarith [hclampMono ht]
      have hi := raw_cap_integral_monotone_energy p (n+2) hN h.beta_pos
        ha0 ha1 hH
      have hi' :
          (∫ z in a..1, rawDensity p (n+2) β
            ((n+2:ℕ)*ep+clamp t₁-Real.log (n+2:ℕ)/(2*cp)) z) ≤
          (∫ z in a..1, rawDensity p (n+2) β
            ((n+2:ℕ)*ep+clamp t₂-Real.log (n+2:ℕ)/(2*cp)) z) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hi
      have hnorm : 0 ≤ (latitudeNormalization (n+1)).toReal := ENNReal.toReal_nonneg
      have hscale : 0 ≤ capScale (n+2) F (1/(2*x)) := capScale_nonneg _ _ _
      change G' n t₁ ≤ G' n t₂
      simp only [G', hn, ↓reduceIte, G]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hi' hnorm) hscale
  have hpointAll : ∀ t : ℝ,
      Tendsto (fun n => G' n t) atTop (𝓝 (g (clamp t))) := by
    intro t
    have hpnt : Tendsto (fun n => G n (clamp t)) atTop
        (𝓝 (g (clamp t))) := by
      simpa only [G,g,μ,q,cp,ep,F] using hpoint (clamp t) (hclampMem t)
    apply hpnt.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [G', show ¬ n ≤ 1 by omega, ↓reduceIte]
  have hgClamp : Continuous (fun t => g (clamp t)) := by
    apply hg.comp
    dsimp [clamp]
    fun_prop
  have huni := uniform_on_compact_of_monotone G' (fun t => g (clamp t))
    hmono hgClamp hpointAll
    (isCompact_Icc : IsCompact (Icc (-L) L))
  rw [Metric.tendstoUniformlyOn_iff] at huni ⊢
  intro η hη
  filter_upwards [huni η hη, eventually_ge_atTop 2] with n hn hn2 t ht
  simpa only [G',show ¬ n ≤ 1 by omega,↓reduceIte,hclampEq t ht,
    G,g,μ,q,cp,ep,F] using hn t ht

end
end SlowEquilibration.SphericalPureCapFullLaplaceUniform
