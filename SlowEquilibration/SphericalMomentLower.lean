-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiBound
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

/-!
# Genuine moment-to-pressure lower bounds

These lemmas formalize the probabilistic step in the constructive spherical
Parisi lower bound. The physical partition and its sharp Gaussian concentration
are the actual ones. Candidate first and second moments remain explicit inputs;
no thermodynamic lower bound or Parisi formula is assumed or claimed here.
-/

noncomputable section
namespace SlowEquilibration.SphericalMomentLower

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine Paley--Zygmund for a nonnegative ordinary random variable.
The moments are actual Bochner integrals under its actual probability law. -/
theorem paleyZygmund_half {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Ω → ℝ) (hY : Measurable Y)
    (hi : Integrable Y ν) (hi₂ : Integrable (fun x => Y x^2) ν)
    (hY0 : ∀ᵐ x ∂ν, 0 ≤ Y x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmean : a ≤ ∫ x, Y x ∂ν) (hsecond : (∫ x, Y x^2 ∂ν) ≤ b) :
    a^2/(4*b) ≤ ν.real {x | a/2 ≤ Y x} := by
  let B : Set Ω := {x | a/2 ≤ Y x}
  have hB : MeasurableSet B := measurableSet_le measurable_const hY
  have hp : ν.real Bᶜ ≤ 1 := by
    simpa only [probReal_univ] using (measureReal_mono (μ := ν) (subset_univ Bᶜ))
  have hcomp : (∫ x in Bᶜ, Y x ∂ν) ≤ a/2 := by
    calc
      _ ≤ ∫ _x in Bᶜ, a/2 ∂ν := by
        apply integral_mono_ae hi.restrict (integrable_const _)
        filter_upwards [ae_restrict_mem hB.compl] with x hx
        change ¬a/2 ≤ Y x at hx
        exact (lt_of_not_ge hx).le
      _ = ν.real Bᶜ*(a/2) := by simp
      _ ≤ a/2 := by nlinarith
  have hsum := integral_add_compl hB hi
  have hlower : a/2 ≤ ∫ x in B, Y x ∂ν := by linarith
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    hY0
    (ae_of_all ν (fun x => show 0 ≤ B.indicator (fun _ => (1 : ℝ)) x from by
      by_cases hx : x ∈ B <;> simp [hx]))
    (show MemLp Y (ENNReal.ofReal 2) ν from by
      simpa using (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr hi₂)
    (show MemLp (B.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal 2) ν from
      memLp_indicator_const _ hB _ (Or.inr (measure_ne_top ν B)))
  have hleft : (∫ x, Y x*B.indicator (fun _ => (1 : ℝ)) x ∂ν) = ∫ x in B, Y x ∂ν := by
    rw [← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hright : (∫ x, (B.indicator (fun _ => (1 : ℝ)) x)^(2 : ℝ) ∂ν) = ν.real B := by
    have he : (fun x => (B.indicator (fun _ => (1 : ℝ)) x)^(2 : ℝ)) =
        B.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [he, integral_indicator hB]
    simp
  rw [hleft, hright] at hHolder
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hHolder
  have hM : 0 ≤ ∫ x, Y x^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  have hP : 0 ≤ ν.real B := measureReal_nonneg
  have hs := (sq_le_sq₀ (show 0 ≤ a/2 by positivity)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr (hlower.trans hHolder)
  rw [mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hP] at hs
  have hmp := mul_le_mul_of_nonneg_right hsecond hP
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hb)).mpr
  change a^2 ≤ ν.real B*(4*b)
  nlinarith

/-- A lower event whose probability exceeds the actual sharp concentration
tail forces a genuine finite-volume quenched pressure lower bound. -/
theorem pressure_lower_of_probability {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 < β) (L ε : ℝ) (hε : 0 < ε)
    (hprob : 2*Real.exp (-(ε^2*(N : ℝ))/(2*β^2*μ.xi 1)) <
      (disorderLaw N μ.maxDegree).real {J | (N : ℝ)*L ≤ Real.log (mixturePartition μ β J)}) :
    L-ε ≤ quenchedPressure N μ β := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1 := by
    rw [covariancePolynomial_mixture]
    exact μ.xi_pos (by norm_num)
  have hc := logPartitionAgainst_pressure_concentration hN (sphereLaw N) (sphereLaw_support hN)
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hcov hβ hε
  change disorderLaw N μ.maxDegree {J | ε*(N : ℝ) ≤
    |Real.log (mixturePartition μ β J)-
      (∫ K, Real.log (mixturePartition μ β K) ∂disorderLaw N μ.maxDegree)|} ≤ _ at hc
  rw [covariancePolynomial_mixture] at hc
  have hcR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (by positivity)] at hcR
  have hmean : (∫ K, Real.log (mixturePartition μ β K) ∂disorderLaw N μ.maxDegree) =
      (N : ℝ)*quenchedPressure N μ β := by
    unfold quenchedPressure
    rw [mul_div_cancel₀ _ hNr.ne']
  by_contra hn
  have hn' : quenchedPressure N μ β < L-ε := lt_of_not_ge hn
  have hsub : {J : Disorder N μ.maxDegree | (N : ℝ)*L ≤ Real.log (mixturePartition μ β J)} ⊆
      {J | ε*(N : ℝ) ≤ |Real.log (mixturePartition μ β J)-
        (∫ K, Real.log (mixturePartition μ β K) ∂disorderLaw N μ.maxDegree)|} := by
    intro J hJ
    change (N : ℝ)*L ≤ Real.log (mixturePartition μ β J) at hJ
    change ε*(N : ℝ) ≤ _
    rw [hmean]
    have hh := mul_lt_mul_of_pos_left hn' hNr
    linarith [le_abs_self (Real.log (mixturePartition μ β J)-(N : ℝ)*quenchedPressure N μ β)]
  have hm := measureReal_mono (μ := disorderLaw N μ.maxDegree) hsub
  exact (not_lt_of_ge (hm.trans hcR)) hprob

/-- The actual moment-to-free-energy step for truncated partitions or
critical-count candidates. The event implication states precisely how the
candidate supplies a physical partition lower event; all its moment inputs
are genuine disorder integrals. -/
theorem pressure_lower_of_candidate_moments {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 < β) (Y : Disorder N μ.maxDegree → ℝ) (hY : Measurable Y)
    (hi : Integrable Y (disorderLaw N μ.maxDegree))
    (hi₂ : Integrable (fun J => Y J^2) (disorderLaw N μ.maxDegree))
    (hY0 : ∀ᵐ J ∂disorderLaw N μ.maxDegree, 0 ≤ Y J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmean : a ≤ ∫ J, Y J ∂disorderLaw N μ.maxDegree)
    (hsecond : (∫ J, Y J^2 ∂disorderLaw N μ.maxDegree) ≤ b)
    (L ε : ℝ) (hε : 0 < ε)
    (hphysical : ∀ᵐ J ∂disorderLaw N μ.maxDegree,
      a/2 ≤ Y J → (N : ℝ)*L ≤ Real.log (mixturePartition μ β J))
    (htail : 2*Real.exp (-(ε^2*(N : ℝ))/(2*β^2*μ.xi 1)) < a^2/(4*b)) :
    L-ε ≤ quenchedPressure N μ β := by
  apply pressure_lower_of_probability hN μ hβ L ε hε
  have hp := paleyZygmund_half (disorderLaw N μ.maxDegree) Y hY hi hi₂ hY0 ha hb hmean hsecond
  have hm := ENNReal.toReal_mono
    (measure_ne_top (disorderLaw N μ.maxDegree)
      {J | (N : ℝ)*L ≤ Real.log (mixturePartition μ β J)}) (measure_mono_ae hphysical)
  exact htail.trans_le (hp.trans hm)

/-- For an actual nonnegative truncated partition Y≤Z, the physical-event
implication is derived from monotonicity of the ordinary logarithm. -/
theorem pressure_lower_of_truncated_partition_moments {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 < β) (Y : Disorder N μ.maxDegree → ℝ) (hY : Measurable Y)
    (hi₂ : Integrable (fun J => Y J^2) (disorderLaw N μ.maxDegree))
    (hY0 : ∀ᵐ J ∂disorderLaw N μ.maxDegree, 0 ≤ Y J)
    (hYZ : ∀ᵐ J ∂disorderLaw N μ.maxDegree, Y J ≤ mixturePartition μ β J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmean : a ≤ ∫ J, Y J ∂disorderLaw N μ.maxDegree)
    (hsecond : (∫ J, Y J^2 ∂disorderLaw N μ.maxDegree) ≤ b)
    (L ε : ℝ) (hε : 0 < ε) (hscale : (N : ℝ)*L ≤ Real.log (a/2))
    (htail : 2*Real.exp (-(ε^2*(N : ℝ))/(2*β^2*μ.xi 1)) < a^2/(4*b)) :
    L-ε ≤ quenchedPressure N μ β := by
  have hZint : Integrable (mixturePartition (N := N) μ β) (disorderLaw N μ.maxDegree) :=
    field_exp_prod_integrable hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β |>.integral_prod_left
  have hi : Integrable Y (disorderLaw N μ.maxDegree) := by
    apply hZint.norm.mono' hY.aestronglyMeasurable
    filter_upwards [hY0,hYZ] with J h0 hle
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (mixturePartition_pos hN μ β J).le]
    exact hle
  apply pressure_lower_of_candidate_moments hN μ hβ Y hY hi hi₂ hY0 ha hb hmean hsecond L ε hε ?_ htail
  filter_upwards [hYZ] with J hJ hlow
  exact hscale.trans (Real.log_le_log (by positivity : 0 < a/2) (hlow.trans hJ))

end SlowEquilibration.SphericalMomentLower
