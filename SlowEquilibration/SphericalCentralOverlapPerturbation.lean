-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianOverlapBounds
public import SlowEquilibration.SphericalHSCentralSecondMoment
public import SlowEquilibration.MeasureCovariance

@[expose] public section

/-! # Cubic central-overlap correction for genuine minimum-degree-three mixtures -/
namespace SlowEquilibration
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual signed finite polynomial is cubically small at the origin if
its genuine supported minimum degree is at least three. -/
theorem FiniteMixture.abs_xi_le_cubic (μ : FiniteMixture) (hd : 3≤μ.minDegree)
    {r : ℝ} (hr : |r|≤1) : |μ.xi r|≤μ.xi 1*|r|^3 := by
  unfold FiniteMixture.xi
  simp only [one_pow,mul_one]
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ p ∈ μ.coeff.support, |μ.coeff p*r^p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ μ.coeff.support, μ.coeff p*|r|^3 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul,abs_of_nonneg (μ.nonneg p),abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (abs_nonneg r) hr (hd.trans (μ.degree_bounds hp).1)) (μ.nonneg p)

namespace SphericalModel
open SphericalBarycenter SphericalForm SphericalAging.HardSphereDynamics

/-- Every continuous function on the genuine sphere pair has every Lp moment. -/
theorem memLp_spherePair_continuous {N : ℕ} (hN : 1≤N) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Vector N × Vector N → G}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p ((sphereLaw N).prod (sphereLaw N)) := by
  let := sphereLaw_probability N
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0:Vector N) (Real.sqrt N))).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [sphereLaw_pair_support hN] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

lemma sphere_pair_sixth_moment_le (N : ℕ) (hN : 1≤N) :
    (∫ z : Vector N × Vector N, |overlap z.1 z.2|^6 ∂(sphereLaw N).prod (sphereLaw N)) ≤
      (64/(N:ℝ)^3)*gaussianSixthMoment+Real.exp (-(N:ℝ)*GaussianShell.rate (1/4)) := by
  let := sphereLaw_probability N
  have hf : Continuous (fun z : Vector N × Vector N => |overlap z.1 z.2|^6) := by
    unfold overlap; fun_prop
  rw [integral_prod _ ((memLp_spherePair_continuous hN hf 1).integrable le_rfl)]
  calc
    _ ≤ ∫ _x : Vector N, (64/(N:ℝ)^3)*gaussianSixthMoment+Real.exp (-(N:ℝ)*GaussianShell.rate (1/4)) ∂sphereLaw N := by
      apply integral_mono_of_nonneg (.of_forall fun _ => integral_nonneg fun _ => by positivity)
        (integrable_const _)
      filter_upwards [sphereLaw_support hN] with x hx
      exact sphere_overlap_sixth_moment_le N hN x hx
    _ = _ := by simp

lemma sphere_pair_exp_square_le (N : ℕ) (hN : 1≤N) {t : ℝ}
    (ht0 : 0≤t) (ht : 4*t<1/2) (htrate : t≤GaussianShell.rate (1/4)) :
    (∫ z : Vector N × Vector N, Real.exp (t*(N:ℝ)*(overlap z.1 z.2)^2)
      ∂(sphereLaw N).prod (sphereLaw N)) ≤ (1-8*t)^(-(1:ℝ)/2)+1 := by
  let := sphereLaw_probability N
  have hf : Continuous (fun z : Vector N × Vector N => Real.exp (t*(N:ℝ)*(overlap z.1 z.2)^2)) := by
    unfold overlap; fun_prop
  rw [integral_prod _ ((memLp_spherePair_continuous hN hf 1).integrable le_rfl)]
  calc
    _ ≤ ∫ _x : Vector N, (1-8*t)^(-(1:ℝ)/2)+1 ∂sphereLaw N := by
      apply integral_mono_of_nonneg (.of_forall fun _ => integral_nonneg fun _ => (Real.exp_pos _).le)
        (integrable_const _)
      filter_upwards [sphereLaw_support hN] with x hx
      exact sphere_overlap_exp_square_le N hN x hx ht0 ht htrate
    _ = _ := by simp

private lemma exp_le_one_add_mul_exp (a : ℝ) : Real.exp a≤1+a*Real.exp a := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-a)) (Real.exp_pos a).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at h
  nlinarith

/-- Genuine finite-volume central-overlap upper estimate. The error vanishes
with N because the actual sixth overlap moment is cubic in N⁻¹. -/
theorem centralOverlapMoment_le_cubic_error (N : ℕ) (hN : 1≤N) (μ : FiniteMixture)
    (hd : 3≤μ.minDegree) (β : ℝ) {δ : ℝ} (hδ : 0≤δ)
    (hsmall : 8*(β^2*μ.xi 1*δ)<1/2)
    (hrate : 2*(β^2*μ.xi 1*δ)≤GaussianShell.rate (1/4)) :
    centralOverlapMoment N (mixtureCoefficients μ) β δ ≤
      1+(β^2*μ.xi 1)*(N:ℝ)*
        Real.sqrt ((64/(N:ℝ)^3)*gaussianSixthMoment+Real.exp (-(N:ℝ)*GaussianShell.rate (1/4)))*
        Real.sqrt ((1-16*(β^2*μ.xi 1*δ))^(-(1:ℝ)/2)+1) := by
  let := sphereLaw_probability N
  let ν := (sphereLaw N).prod (sphereLaw N)
  let A := β^2*μ.xi 1
  have hA : 0≤A := mul_nonneg (sq_nonneg β) (μ.xi_pos zero_lt_one).le
  let f := fun z : Vector N × Vector N => |overlap z.1 z.2|^3
  let g := fun z : Vector N × Vector N => Real.exp (A*δ*(N:ℝ)*(overlap z.1 z.2)^2)
  have hf : Continuous f := by unfold f overlap; fun_prop
  have hg : Continuous g := by unfold g overlap; fun_prop
  have hLpF := memLp_spherePair_continuous hN hf 2
  have hLpG := memLp_spherePair_continuous hN hg 2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (.of_forall fun z => by positivity : 0≤ᵐ[ν] f)
    (.of_forall fun z => (Real.exp_pos _).le : 0≤ᵐ[ν] g) (show MemLp f (ENNReal.ofReal 2) ν from by simpa only [ν,ENNReal.ofReal_ofNat] using hLpF)
    (show MemLp g (ENNReal.ofReal 2) ν from by simpa only [ν,ENNReal.ofReal_ofNat] using hLpG)
  have hcs' : (∫ z, f z*g z ∂ν)≤
      Real.sqrt (∫ z, |overlap z.1 z.2|^6 ∂ν)*
        Real.sqrt (∫ z, Real.exp ((2*(A*δ))*(N:ℝ)*(overlap z.1 z.2)^2) ∂ν) := by
    simp only [Real.rpow_two,← Real.sqrt_eq_rpow] at hcs
    have hfPow : (fun z : Vector N × Vector N => (f z)^2)=fun z => |overlap z.1 z.2|^6 := by
      funext z
      simp only [f,← pow_mul]
    have hgPow : (fun z : Vector N × Vector N => (g z)^2)=
        fun z => Real.exp ((2*(A*δ))*(N:ℝ)*(overlap z.1 z.2)^2) := by
      funext z
      simp only [g,pow_two,← Real.exp_add]
      congr 1
      ring_nf
    rw [hfPow,hgPow] at hcs
    exact hcs
  have hsix := sphere_pair_sixth_moment_le N hN
  have hexp := sphere_pair_exp_square_le N hN (t := 2*(A*δ))
    (mul_nonneg (by norm_num) (mul_nonneg hA hδ))
    (by dsimp [A]; linarith) (by simpa only [A] using hrate)
  have hprod : (∫ z, f z*g z ∂ν) ≤
      Real.sqrt ((64/(N:ℝ)^3)*gaussianSixthMoment+Real.exp (-(N:ℝ)*GaussianShell.rate (1/4)))*
      Real.sqrt ((1-16*(A*δ))^(-(1:ℝ)/2)+1) := by
    apply hcs'.trans
    apply mul_le_mul (Real.sqrt_le_sqrt hsix) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    convert Real.sqrt_le_sqrt hexp using 1
    congr 2
    ring_nf
  have hcentral : Integrable (fun z : Vector N × Vector N =>
      (smallOverlap δ).indicator (fun w => Real.exp ((N:ℝ)*β^2*covariancePolynomial (mixtureCoefficients μ)
        (overlap w.1 w.2))) z) ν := by
    apply ((memLp_spherePair_continuous hN (by unfold overlap covariancePolynomial; fun_prop) 1).integrable le_rfl).indicator
    exact smallOverlap_measurable δ
  have hdom := (integrable_const (1:ℝ)).add ((hLpF.integrable_mul hLpG).const_mul (A*N))
  have hbound : centralOverlapMoment N (mixtureCoefficients μ) β δ≤
      ∫ z, 1+(A*(N:ℝ))*(f z*g z) ∂ν := by
    apply integral_mono_ae hcentral hdom
    filter_upwards [sphereLaw_pair_support hN] with z hz
    have hr : |overlap z.1 z.2|≤1 := abs_le.mpr (overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2)
    by_cases hs : z∈smallOverlap δ
    · rw [Set.indicator_of_mem hs]
      have hc := μ.abs_xi_le_cubic hd hr
      have hξ : (N:ℝ)*β^2*μ.xi (overlap z.1 z.2)≤(A*(N:ℝ))*|overlap z.1 z.2|^3 := by
        have hm := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hc) (by positivity : 0≤(N:ℝ)*β^2)
        convert hm using 1
        dsimp [A]
        ring_nf
      have hδpow : |overlap z.1 z.2|^3≤δ*(overlap z.1 z.2)^2 := by
        have hm := mul_le_mul_of_nonneg_right (show |overlap z.1 z.2|≤δ from le_of_lt hs) (sq_nonneg (overlap z.1 z.2))
        convert hm using 1
        rw [pow_succ,sq_abs]
        ring_nf
      have hexp' : Real.exp ((A*(N:ℝ))*|overlap z.1 z.2|^3)≤g z := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hδpow (by positivity : 0≤A*(N:ℝ))
        convert hm using 1
        ring_nf
      rw [covariancePolynomial_mixture]
      calc
        _ ≤ Real.exp ((A*(N:ℝ))*|overlap z.1 z.2|^3) := Real.exp_le_exp.mpr hξ
        _ ≤ 1+((A*(N:ℝ))*|overlap z.1 z.2|^3)*Real.exp ((A*(N:ℝ))*|overlap z.1 z.2|^3) :=
          exp_le_one_add_mul_exp _
        _ ≤ _ := by
          apply add_le_add le_rfl
          simpa only [f,Pi.mul_apply,mul_assoc] using mul_le_mul_of_nonneg_left hexp' (by positivity : 0≤A*(N:ℝ)*|overlap z.1 z.2|^3)
    · rw [Set.indicator_of_notMem hs]
      dsimp [f,g]
      positivity
  have hfg : Integrable (fun z => f z*g z) ν := hLpF.integrable_mul hLpG
  have he : (∫ z, 1+(A*(N:ℝ))*(f z*g z) ∂ν)=1+(A*(N:ℝ))*(∫ z, f z*g z ∂ν) := by
    have hi := integral_add (integrable_const (1:ℝ) (μ := ν)) (hfg.const_mul (A*N))
    simpa only [Pi.add_apply,integral_const,probReal_univ,one_smul,integral_const_mul] using hi
  rw [he] at hbound
  have hm := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤A*(N:ℝ))
  exact hbound.trans (by dsimp [A] at hm; nlinarith only [hm])

end SphericalModel
end
end SlowEquilibration
