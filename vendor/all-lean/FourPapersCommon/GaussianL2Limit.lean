module

public import FourPapersCommon.L2Moments
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! Gaussian laws are closed under genuine L² limits of random variables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

theorem norm_exp_real_mul_I_sub_le (a b : ℝ) :
    ‖exp ((a:ℂ)*I)-exp ((b:ℂ)*I)‖≤‖a-b‖ := by
  have he : exp ((a:ℂ)*I)-exp ((b:ℂ)*I)=
      exp ((b:ℂ)*I)*(exp (I*(a-b))-1) := by
    rw [mul_sub,mul_one,←exp_add]
    congr 1
    congr 1 <;> ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=a-b))

theorem gaussianCharIncrement_lipschitz (L : StrongDual ℝ E) :
    LipschitzWith ‖L‖₊ (fun x:E=>exp ((L x:ℂ)*I)-1) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,sub_sub_sub_cancel_right,dist_eq_norm]
  change ‖exp ((L x:ℂ)*I)-exp ((L y:ℂ)*I)‖≤‖L‖*‖x-y‖
  exact (norm_exp_real_mul_I_sub_le (L x) (L y)).trans
    (by simpa only [←map_sub] using L.le_opNorm (x-y))

theorem continuous_charFunDual_l2 (L : StrongDual ℝ E) :
    Continuous (fun X : Lp E 2 P => charFunDual (P.map X) L) := by
  let hg:=gaussianCharIncrement_lipschitz L
  have h0 : (fun x:E=>exp ((L x:ℂ)*I)-1) 0=0 := by simp
  have he (X : Lp E 2 P) : charFunDual (P.map X) L=
      (∫ω,(hg.compLp h0 X) ω ∂P)+1 := by
    rw [charFunDual_apply,integral_map (Lp.aestronglyMeasurable X).aemeasurable (by fun_prop)]
    have hi : Integrable (fun ω=>exp ((L (X ω):ℂ)*I)) P :=
      (integrable_const (1:ℝ)).mono' (by fun_prop)
        (.of_forall fun ω=>by simp)
    rw [integral_congr_ae (hg.coeFn_compLp h0 X)]
    simp only [Function.comp_def]
    rw [integral_sub hi (integrable_const (1:ℂ))]
    simp
  simp_rw [he]
  exact (continuous_integral_l2.comp (hg.continuous_compLp h0)).add continuous_const

theorem hasGaussianLaw_of_L2_tendsto {Xn : ℕ→Lp E 2 P} {X : Lp E 2 P}
    (hG : ∀n,HasGaussianLaw (Xn n) P) (hlim : Tendsto Xn atTop (𝓝 X)) :
    HasGaussianLaw X P := by
  apply (hasGaussianLaw_iff_charFunDual_map_eq (Lp.aestronglyMeasurable X).aemeasurable).mpr
  intro L
  let Y : Lp E 2 P→Lp ℝ 2 P := L.compLpL 2 P
  have hy : Tendsto (fun n=>Y (Xn n)) atTop (𝓝 (Y X)) :=
    (L.compLpL 2 P).continuous.tendsto X |>.comp hlim
  have hmean (Z : Lp E 2 P) : (∫ω,(Y Z) ω ∂P)=∫ω,L (Z ω) ∂P :=
    integral_congr_ae (L.coeFn_compLpL Z)
  have hvar (Z : Lp E 2 P) : Var[Y Z;P]=Var[L ∘ Z;P] :=
    variance_congr (L.coeFn_compLpL Z)
  have hm := (continuous_integral_l2.tendsto (Y X)).comp hy
  have hv := (continuous_variance_l2.tendsto (Y X)).comp hy
  change Tendsto (fun n=>∫ω,(Y (Xn n)) ω ∂P) atTop (𝓝 (∫ω,(Y X) ω ∂P)) at hm
  change Tendsto (fun n=>Var[Y (Xn n);P]) atTop (𝓝 Var[Y X;P]) at hv
  simp only [hmean,hvar] at hm hv
  have hr : Tendsto (fun n=>exp ((∫ω,L (Xn n ω) ∂P:ℝ)*I-Var[L ∘ Xn n;P]/2))
      atTop (𝓝 (exp ((∫ω,L (X ω) ∂P:ℝ)*I-Var[L ∘ X;P]/2))) := by
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (((Complex.continuous_ofReal.tendsto _).comp hm).mul_const I |>.sub
        (((Complex.continuous_ofReal.tendsto _).comp hv).div_const 2))
  have hc := (continuous_charFunDual_l2 L).tendsto X |>.comp hlim
  have he (n : ℕ) := (hG n).charFunDual_map_eq_fun L
  change Tendsto (fun n=>charFunDual (P.map (Xn n)) L) atTop
    (𝓝 (charFunDual (P.map X) L)) at hc
  simp only [he] at hc
  exact tendsto_nhds_unique hc hr

end FourPapersCommon
