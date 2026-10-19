-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteModel
public import SlowEquilibration.GaussianSummableSeries
public import Mathlib.Probability.Independence.Integration

/-! The source infinite field is an actual L² sum under the original countable
ordered-tensor disorder. Its Gaussian law and almost-everywhere convergence
are consequences of the coefficient summability, not extra premises. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine Hilbert-space sum of the weighted pure fields. -/
def fieldLp {N : ℕ} (μ : InfiniteMixture) (x : Vector N) : Lp ℝ 2 (disorderLaw N) :=
  ∑' p,blockLp μ p x

theorem fieldLp_coe_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    fieldLp μ x =ᵐ[disorderLaw N] fun J => field μ J x := by
  have hen : ∑' p,‖blockLp μ p x‖ₑ≠⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr
      (NNReal.summable_coe.mp (summable_blockLp_norm hN μ x hx))
  have hc : ∀ᵐ J ∂disorderLaw N,∀ p,blockLp μ p x J=block μ p J x := by
    rw [ae_all_iff]
    exact fun p => (block_memLp μ p x).coeFn_toLp
  filter_upwards [Lp.coeFn_tsum hen,hc] with J hJ he
  rw [fieldLp,hJ,field]
  exact tsum_congr he

theorem field_memLp {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    MemLp (fun J => field μ J x) 2 (disorderLaw N) :=
  (memLp_congr_ae (fieldLp_coe_ae hN μ x hx)).1 (Lp.memLp (fieldLp μ x))

theorem field_hasSum_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    ∀ᵐ J ∂disorderLaw N,HasSum (fun p => block μ p J x) (field μ J x) :=
  GaussianSummableSeries.hasSum_tsum_ae (fun p => block_memLp μ p x)
    (summable_blockLp_norm hN μ x hx)

theorem field_hasGaussianLaw {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    HasGaussianLaw (fun J => field μ J x) (disorderLaw N) :=
  GaussianSummableSeries.hasGaussianLaw_tsum (fun p => block_memLp μ p x)
    (summable_blockLp_norm hN μ x hx) (partialSum_hasGaussianLaw μ x)

theorem field_mean {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    ∫ J,field μ J x ∂disorderLaw N=0 := by
  rw [← integral_congr_ae (fieldLp_coe_ae hN μ x hx)]
  rw [← FourPapersCommon.l2Expectation_eq_integral,fieldLp,
    ContinuousLinearMap.map_tsum _ (summable_blockLp_norm hN μ x hx).of_norm]
  have he (p : ℕ) : FourPapersCommon.l2Expectation (blockLp μ p x)=0 := by
    rw [FourPapersCommon.l2Expectation_eq_integral]
    unfold blockLp
    rw [integral_congr_ae (block_memLp μ p x).coeFn_toLp,block_mean]
  simp_rw [he,tsum_zero]

theorem blockLp_inner {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (p q : ℕ) (x y : Vector N) :
    ⟪blockLp μ p x,blockLp μ q y⟫ =
      if p=q then (N:ℝ)*μ.coeff (p+2)*(overlap x y)^(p+2) else 0 := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  unfold blockLp
  rw [integral_congr_ae ((block_memLp μ q y).coeFn_toLp.fun_mul
    (block_memLp μ p x).coeFn_toLp)]
  by_cases hpq : p=q
  · subst q
    rw [if_pos rfl]
    simpa only [mul_comm] using block_product_integral hN μ p x y
  · rw [if_neg hpq]
    have hi := ((independent_degrees N).indepFun hpq).comp
      (Real.sqrt (μ.coeff (p+2)) • pureFieldCLM N (p+2) x).measurable
      (Real.sqrt (μ.coeff (q+2)) • pureFieldCLM N (q+2) y).measurable
    have hib : IndepFun (fun J => block μ p J x) (fun J => block μ q J y)
        (disorderLaw N) := by
      simpa only [Function.comp_def,smul_apply,smul_eq_mul,pureFieldCLM_apply,block] using hi
    have he := hib.symm.integral_mul_eq_mul_integral
      (block_memLp μ q y).aestronglyMeasurable (block_memLp μ p x).aestronglyMeasurable
    simpa only [Pi.mul_apply,block_mean,mul_zero] using he

theorem overlap_abs_le_one_of_norm_sq_le {N : ℕ} (hN : 0<N) (x y : Vector N)
    (hx : ‖x‖^2≤(N:ℝ)) (hy : ‖y‖^2≤(N:ℝ)) : |overlap x y|≤1 := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  rw [overlap,abs_div,abs_of_pos hNr]
  apply (div_le_one hNr).2
  have hinner := abs_real_inner_le_norm x y
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem fieldLp_inner {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x y : Vector N) (hx : ‖x‖^2≤(N:ℝ)) (hy : ‖y‖^2≤(N:ℝ)) :
    ⟪fieldLp μ x,fieldLp μ y⟫=(N:ℝ)*μ.xi (overlap x y) := by
  have hsx := (summable_blockLp_norm hN μ x hx).of_norm
  have hsy := (summable_blockLp_norm hN μ y hy).of_norm
  have hp (p : ℕ) : ⟪blockLp μ p x,fieldLp μ y⟫=
      (N:ℝ)*μ.coeff (p+2)*(overlap x y)^(p+2) := by
    change (innerSL ℝ (blockLp μ p x)) (∑' q,blockLp μ q y)=_
    rw [ContinuousLinearMap.map_tsum _ hsy]
    simp only [innerSL_apply_apply,blockLp_inner hN]
    rw [tsum_eq_single p]
    · simp
    · intro q hq
      simp [Ne.symm hq]
  calc
    _ = ∑' p,⟪blockLp μ p x,fieldLp μ y⟫ := by
      exact (innerSL ℝ).flip (fieldLp μ y) |>.map_tsum hsx
    _ = ∑' p,(N:ℝ)*(μ.coeff (p+2)*(overlap x y)^(p+2)) := by
      simp_rw [hp,mul_assoc]
    _ = (N:ℝ)*μ.xi (overlap x y) := by
      rw [tsum_mul_left]
      congr 1
      have hh := (μ.summable_xi (overlap_abs_le_one_of_norm_sq_le hN x y hx hy)).sum_add_tsum_nat_add 2
      simpa [InfiniteMixture.xi,Finset.sum_range_succ,μ.zero_below_two 0 (by omega),
        μ.zero_below_two 1 (by omega)] using hh

theorem field_product_integral {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x y : Vector N) (hx : ‖x‖^2≤(N:ℝ)) (hy : ‖y‖^2≤(N:ℝ)) :
    ∫ J,field μ J x*field μ J y ∂disorderLaw N=(N:ℝ)*μ.xi (overlap x y) := by
  rw [← fieldLp_inner hN μ x y hx hy,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  apply integral_congr_ae
  filter_upwards [fieldLp_coe_ae hN μ x hx,fieldLp_coe_ae hN μ y hy] with J hJx hJy
  rw [hJx,hJy,mul_comm]

end SlowEquilibration.SphericalInfiniteModel
