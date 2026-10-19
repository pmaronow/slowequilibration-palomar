module
public import FRSB.ConstantMassStochasticHeat
public import FRSB.ConstantMassGrowth
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Genuine Gaussian laws and square integrability for the unbounded
Cole--Hopf observable and its Brownian stochastic coefficient. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000

theorem hasLaw_zeroDriftBrownian (β : ℝ) (l : ℝ≥0) (y : ℝ) (t : ℝ≥0) :
    HasLaw (zeroDriftBrownian β l y t) (gaussianReal y (β^2*(t : ℝ)).toNNReal)
      canonicalBrownianMeasure := by
  have hh := gaussianReal_const_add (gaussianReal_const_mul
    ((isBrownianReal_canonicalBrownian.toIsPreBrownianReal.shift l).hasLaw_eval t) β) y
  have hv : NNReal.mk (β^2) (sq_nonneg β)*t = (β^2*(t : ℝ)).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) t.coe_nonneg)]
  change HasLaw (fun sample => y+β*(canonicalBrownian (l+t) sample-canonicalBrownian l sample))
    (gaussianReal y (β^2*(t : ℝ)).toNNReal) canonicalBrownianMeasure
  simpa only [mul_zero,zero_add,hv] using hh

theorem memLp_two_exp_parisiPotential_gaussian (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (m y : ℝ) (v : ℝ≥0) :
    MemLp (fun x => Real.exp (m*parisiPotential β μ (s,x))) 2 (gaussianReal y v) := by
  have hm : Continuous (fun x => Real.exp (m*parisiPotential β μ (s,x))) := by
    exact Real.continuous_exp.comp (((continuous_parisiPotential β μ).comp
      (continuous_const.prodMk continuous_id)).const_mul m)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hg : ColeHopfFoundation.ProbabilityTheory.HasExpGrowth
      (fun x => Real.exp (m*parisiPotential β μ (s,x))^2) := by
    refine ⟨Real.exp (2*|m| * β^2),2*|m|,by positivity,fun x => ?_⟩
    have hu := parisiPotential_absolute_growth β μ s x hs
    have hbound : m*parisiPotential β μ (s,x) ≤ |m| * (β^2+|x|) := by
      have hh := le_abs_self (m*parisiPotential β μ (s,x))
      rw [abs_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hu (abs_nonneg m))
    change |Real.exp (m*parisiPotential β μ (s,x))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ = Real.exp (2*m*parisiPotential β μ (s,x)) := by
        rw [pow_two,←Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (2*|m| * β^2+2*|m| * |x|) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := Real.exp_add _ _
  exact hg.integrable_gaussianReal (hm.pow 2).aestronglyMeasurable

theorem memLp_two_constantMassHeatObservable (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (m : ℝ) (l : ℝ≥0) (y : ℝ) (t : ℝ≥0) :
    MemLp (fun sample => Real.exp (m*parisiPotential β μ (s,zeroDriftBrownian β l y t sample)))
      2 canonicalBrownianMeasure := by
  have hh := (hasLaw_zeroDriftBrownian β l y t).memLp_comp
    (memLp_two_exp_parisiPotential_gaussian β μ s hs m y _)
  simpa only [Function.comp_def] using hh

theorem memLp_two_constantMassHeatCoefficient (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (m : ℝ) (l : ℝ≥0) (y : ℝ) (t : ℝ≥0) :
    MemLp (fun sample => m*Real.exp (m*parisiPotential β μ (s,zeroDriftBrownian β l y t sample))*
      parisiGradient β μ (s,zeroDriftBrownian β l y t sample)) 2 canonicalBrownianMeasure := by
  have hX := (hasLaw_zeroDriftBrownian β l y t).aemeasurable
  have hU : Measurable (fun x => Real.exp (m*parisiPotential β μ (s,x))) := by
    exact (Real.continuous_exp.comp (((continuous_parisiPotential β μ).comp
      (continuous_const.prodMk continuous_id)).const_mul m)).measurable
  have hB : Measurable (fun x => parisiGradient β μ (s,x)) :=
    ((continuous_parisiGradient β μ).comp (continuous_const.prodMk continuous_id)).measurable
  apply ((memLp_two_constantMassHeatObservable β μ s hs m l y t).const_mul |m|).mono'
    (((hU.comp_aemeasurable hX).const_mul m).mul (hB.comp_aemeasurable hX)).aestronglyMeasurable
  exact .of_forall fun sample => by
    simp only [Pi.mul_apply,Function.comp_def]
    rw [norm_mul,norm_mul,Real.norm_eq_abs m,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (norm_parisiGradient_le_one β μ _)
      (mul_nonneg (abs_nonneg m) (Real.exp_pos _).le)).trans_eq (mul_one _)

/-- The expectation vanishes for the actual stochastic endpoint
difference, including both endpoints of a constant-CDF cell. -/
theorem integral_constantMassHeat_difference_eq_zero (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (l r : ℝ≥0)
    (hl : (l : ℝ) ∈ Icc a b) (hlr : l ≤ r) (hr : (r : ℝ) ≤ b) (y : ℝ) :
    (∫ sample, Real.exp (m*parisiPotential β μ
      ((r : ℝ),zeroDriftBrownian β l y (r-l) sample)) -
        Real.exp (m*parisiPotential β μ ((l : ℝ),y)) ∂canonicalBrownianMeasure) = 0 := by
  have hr0 : 0 ≤ (r : ℝ) := r.coe_nonneg
  have hr01 : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hr0,hr.trans hb⟩
  have hi := (memLp_two_constantMassHeatObservable β μ r hr01 m l y (r-l)).integrable (by norm_num)
  rw [integral_sub hi (integrable_const _)]
  have hmeas : Measurable (fun x => Real.exp (m*parisiPotential β μ ((r : ℝ),x))) := by
    exact (Real.continuous_exp.comp (((continuous_parisiPotential β μ).comp
      (continuous_const.prodMk continuous_id)).const_mul m)).measurable
  have he := (hasLaw_zeroDriftBrownian β l y (r-l)).integral_comp hmeas.aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [he]
  have hm0 : 0 ≤ m := by
    rw [←hc a ⟨le_rfl,hab⟩]
    exact parisiCDF_nonneg μ a
  by_cases hm : m = 0
  · simp [hm]
  · have hv : 0 ≤ β^2*((r : ℝ)-l) := mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hlr))
    have hheat := parisiPotential_exp_heat_on_constant_interval β hβ μ ha hab hb
      (lt_of_le_of_ne hm0 (Ne.symm hm)) hc hl ⟨by exact_mod_cast hlr,hr⟩ y
    rw [heatSemigroup_eq_gaussian_integral _ hv _ hmeas y] at hheat
    simp only [NNReal.coe_sub hlr] at he ⊢
    rw [←hheat]
    simp [Measure.real]

end FRSB
