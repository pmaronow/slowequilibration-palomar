-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalBorderSchurExpectation
public import SlowEquilibration.CommonHessianRealMomentDifference

/-! True ordinary every-real-q determinant error transfer on a genuine
Schur gap, with actual high moments controlling its rare complement. -/
@[expose] public section
namespace SlowEquilibration.BorderSchurExpectation
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open GaussianQuadraticVariance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

lemma rpow_square_eq_double {x:ℝ} (hx:0 ≤ x) (q:ℝ):
    (x^q)^2=x^(2*q):=by
  rw [←Real.rpow_two,←Real.rpow_mul hx]
  congr 1
  ring

/-- Actual q-moment transfer under a proved good-event Schur inequality.
Every moment is an ordinary integral on the original probability space. -/
theorem integral_q_error_of_good_event {Ω:Type*} [MeasurableSpace Ω]
    (μ:Measure Ω) [IsProbabilityMeasure μ] (D B T:Ω→ℝ)
    (hD:Measurable D) (hB:Measurable B) (hT:Measurable T)
    (s q:ℝ) (hq:0 ≤ q)
    (hD2q:Integrable (fun x=>|D x|^(2*q)) μ)
    (hB2q:Integrable (fun x=>|B x|^(2*q)) μ)
    (hT2q:Integrable (fun x=>|T x-s|^(2*q)) μ)
    (G:Set Ω) (hG:MeasurableSet G)
    (hgood:∀ᵐ x ∂μ,x∈G → |D x-|s| *B x| ≤ |B x| *|T x-s|) :
    Integrable (fun x=>|D x-|s| *B x|^q) μ ∧
      (∫ x,|D x-|s| *B x|^q ∂μ) ≤
        Real.sqrt (∫ x,|B x|^(2*q) ∂μ)*Real.sqrt (∫ x,|T x-s|^(2*q) ∂μ)+
        (2:ℝ)^q*(Real.sqrt (∫ x,|D x|^(2*q) ∂μ)+
          |s|^q*Real.sqrt (∫ x,|B x|^(2*q) ∂μ))*Real.sqrt (μ.real Gᶜ):=by
  let Dq:=fun x=>|D x|^q
  let Bq:=fun x=>|B x|^q
  let Tq:=fun x=>|T x-s|^q
  have hDM:MemLp Dq 2 μ:=(memLp_two_iff_integrable_sq (hD.abs.pow_const q).aestronglyMeasurable).mpr
    (by simpa only [Dq,rpow_square_eq_double (abs_nonneg _)] using hD2q)
  have hBM:MemLp Bq 2 μ:=(memLp_two_iff_integrable_sq (hB.abs.pow_const q).aestronglyMeasurable).mpr
    (by simpa only [Bq,rpow_square_eq_double (abs_nonneg _)] using hB2q)
  have hTM:MemLp Tq 2 μ:=(memLp_two_iff_integrable_sq ((hT.sub_const s).abs.pow_const q).aestronglyMeasurable).mpr
    (by simpa only [Tq,rpow_square_eq_double (abs_nonneg _)] using hT2q)
  have hProd:Integrable (fun x=>Bq x*Tq x) μ:=memLp_one_iff_integrable.mp (hBM.mul hTM)
  have hDbad:Integrable (Gᶜ.indicator Dq) μ:=(hDM.integrable (by norm_num)).indicator hG.compl
  have hBbad:Integrable (Gᶜ.indicator Bq) μ:=(hBM.integrable (by norm_num)).indicator hG.compl
  let R:=fun x=>Bq x*Tq x+(2:ℝ)^q*Gᶜ.indicator Dq x+
    (2:ℝ)^q*|s|^q*Gᶜ.indicator Bq x
  have hR:Integrable R μ:=(hProd.add (hDbad.const_mul ((2:ℝ)^q))).add
    (hBbad.const_mul ((2:ℝ)^q*|s|^q))
  have hp:∀ᵐ x ∂μ,|D x-|s| *B x|^q ≤ R x:=by
    filter_upwards [hgood] with x hx
    by_cases hxG:x∈G
    · have hxGc:x∉Gᶜ:=by simpa only [mem_compl_iff,not_not] using hxG
      dsimp only [R]
      simp only [Set.indicator_of_notMem hxGc,mul_zero,add_zero]
      exact (Real.rpow_le_rpow (abs_nonneg _) (hx hxG) hq).trans_eq
        (Real.mul_rpow (abs_nonneg _) (abs_nonneg _))
    · have hab:|D x-|s| *B x| ≤ |D x|+|s| *|B x|:=by
        simpa only [abs_mul,abs_abs] using abs_sub (D x) (|s| *B x)
      have hh:|D x-|s| *B x|^q ≤ (2:ℝ)^q*(Dq x+|s|^q*Bq x):=by
        have hpq:=(Real.rpow_le_rpow (abs_nonneg _) hab hq).trans
          (nonnegative_add_rpow_bound (abs_nonneg _) (by positivity : 0 ≤ |s| *|B x|) hq)
        simpa only [Dq,Bq,Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] using hpq
      dsimp only [R]
      simp only [Set.indicator_of_mem (show x∈Gᶜ from hxG)]
      have hprod0:0 ≤ Bq x*Tq x:=by dsimp only [Bq,Tq];positivity
      nlinarith [hh]
  have hErr:Integrable (fun x=>|D x-|s| *B x|^q) μ:=hR.mono'
    ((hD.sub (hB.const_mul |s|)).abs.pow_const q).aestronglyMeasurable
    (by filter_upwards [hp] with x hx;rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)];exact hx)
  refine ⟨hErr,(integral_mono_ae hErr hR hp).trans ?_⟩
  have hSplit:(∫ x,R x ∂μ)=(∫ x,Bq x*Tq x ∂μ)+(2:ℝ)^q*(∫ x,Gᶜ.indicator Dq x ∂μ)+
      (2:ℝ)^q*|s|^q*(∫ x,Gᶜ.indicator Bq x ∂μ):=by
    dsimp only [R]
    have h1:=integral_add (f:=fun x=>Bq x*Tq x+(2:ℝ)^q*Gᶜ.indicator Dq x)
      (g:=fun x=>(2:ℝ)^q*|s|^q*Gᶜ.indicator Bq x)
      (hProd.add (hDbad.const_mul ((2:ℝ)^q))) (hBbad.const_mul ((2:ℝ)^q*|s|^q))
    have h2:=integral_add (f:=fun x=>Bq x*Tq x) (g:=fun x=>(2:ℝ)^q*Gᶜ.indicator Dq x)
      hProd (hDbad.const_mul ((2:ℝ)^q))
    rw [h1,h2,integral_const_mul,integral_const_mul]
  rw [hSplit]
  have hProdBound:=integral_abs_mul_le_sqrt_sq hBM hTM
  have hDBound:=integral_indicator_abs_le_sqrt_sq hDM hG.compl
  have hBBound:=integral_indicator_abs_le_sqrt_sq hBM hG.compl
  have hdabs (x):|Dq x|=Dq x:=abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)
  have hbabs (x):|Bq x|=Bq x:=abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)
  have htabs (x):|Tq x|=Tq x:=abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)
  simp only [hdabs,hbabs,htabs,Dq,Bq,Tq,rpow_square_eq_double (abs_nonneg _)] at hProdBound hDBound hBBound
  exact (add_le_add (add_le_add hProdBound (mul_le_mul_of_nonneg_left hDBound (by positivity)))
    (mul_le_mul_of_nonneg_left hBBound (by positivity))).trans_eq (by ring)

end
end SlowEquilibration.BorderSchurExpectation
