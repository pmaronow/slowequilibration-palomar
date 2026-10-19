module
public import FRSB.ConstantMassGaussianMoments
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Literal exponential heat coefficients are square integrable jointly
in time and Brownian sample, with explicit Gaussian exponential bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000

private theorem exp_abs_le_exp_add (c x : ℝ) (_hc : 0 ≤ c) :
    Real.exp (c*|x|) ≤ Real.exp (c*x)+Real.exp (-c*x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx]
    have he : c*(-x) = -c*x := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem integrable_exp_mul_abs_gaussian (y c : ℝ) (v : ℝ≥0) (hc : 0 ≤ c) :
    Integrable (fun x => Real.exp (c*|x|)) (gaussianReal y v) := by
  apply ((integrable_exp_mul_gaussianReal (μ := y) (v := v) c).add
    (integrable_exp_mul_gaussianReal (μ := y) (v := v) (-c))).mono'
      (Real.continuous_exp.comp (continuous_abs.const_mul c)).aestronglyMeasurable
  exact .of_forall fun x => by
    change ‖Real.exp (c*|x|)‖ ≤ Real.exp (c*x)+Real.exp (-c*x)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_abs_le_exp_add c x hc

theorem integral_exp_mul_abs_gaussian_le (y c : ℝ) (v : ℝ≥0) (hc : 0 ≤ c) :
    (∫ x,Real.exp (c*|x|) ∂gaussianReal y v) ≤
      2*Real.exp (|y| *c+(v : ℝ)*c^2/2) := by
  have hi := integrable_exp_mul_abs_gaussian y c v hc
  have h1 := integrable_exp_mul_gaussianReal (μ := y) (v := v) c
  have h2 := integrable_exp_mul_gaussianReal (μ := y) (v := v) (-c)
  have hh := integral_mono hi (h1.add h2) (exp_abs_le_exp_add c · hc)
  simp only [Pi.add_apply] at hh
  rw [integral_add h1 h2] at hh
  have he1 : (∫ x,Real.exp (c*x) ∂gaussianReal y v) = Real.exp (y*c+(v : ℝ)*c^2/2) :=
    congrFun (mgf_fun_id_gaussianReal (μ := y) (v := v)) c
  have he2 : (∫ x,Real.exp (-c*x) ∂gaussianReal y v) = Real.exp (-y*c+(v : ℝ)*c^2/2) := by
    simpa only [mgf,neg_sq,mul_neg,neg_mul] using
      congrFun (mgf_fun_id_gaussianReal (μ := y) (v := v)) (-c)
  rw [he1,he2] at hh
  have hpos := mul_le_mul_of_nonneg_right (le_abs_self y) hc
  have hneg := mul_le_mul_of_nonneg_right (neg_le_abs y) hc
  have hsum : Real.exp (y*c+(v : ℝ)*c^2/2)+Real.exp (-y*c+(v : ℝ)*c^2/2) ≤
      Real.exp (|y| *c+(v : ℝ)*c^2/2)+Real.exp (|y| *c+(v : ℝ)*c^2/2) :=
    add_le_add (Real.exp_le_exp.mpr (add_le_add hpos le_rfl))
      (Real.exp_le_exp.mpr (add_le_add hneg le_rfl))
  exact hh.trans (by nlinarith [hsum])

private theorem heat_coefficient_sq_pointwise (β m : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    (m*Real.exp (m*parisiPotential β μ (s,x))*parisiGradient β μ (s,x))^2 ≤
      m^2*Real.exp (2*|m| *β^2)*Real.exp (2*|m| *|x|) := by
  have hu := parisiPotential_absolute_growth β μ s x hs
  have hg := norm_parisiGradient_le_one β μ (s,x)
  rw [Real.norm_eq_abs] at hg
  have hg2 : parisiGradient β μ (s,x)^2 ≤ 1 := by
    have hh := (sq_le_sq₀ (abs_nonneg (parisiGradient β μ (s,x))) zero_le_one).mpr hg
    simpa only [sq_abs,one_pow] using hh
  have hm : m*parisiPotential β μ (s,x) ≤ |m| *(β^2+|x|) := by
    calc
      _ ≤ |m*parisiPotential β μ (s,x)| := le_abs_self _
      _ = _ := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (abs_nonneg m)
  have he : Real.exp (m*parisiPotential β μ (s,x))^2 ≤
      Real.exp (2*|m| *β^2)*Real.exp (2*|m| *|x|) := by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ = m^2*Real.exp (m*parisiPotential β μ (s,x))^2*parisiGradient β μ (s,x)^2 := by ring
    _ ≤ m^2*Real.exp (m*parisiPotential β μ (s,x))^2*1 :=
      mul_le_mul_of_nonneg_left hg2 (by positivity)
    _ ≤ _ := by simpa only [mul_one,mul_assoc] using mul_le_mul_of_nonneg_left he (sq_nonneg m)

 theorem integral_constantMassHeatCoefficient_sq_le (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (m : ℝ) (l : ℝ≥0) (y : ℝ)
    (t T : ℝ≥0) (ht : t ≤ T) :
    (∫ sample,(m*Real.exp (m*parisiPotential β μ (s,zeroDriftBrownian β l y t sample))*
      parisiGradient β μ (s,zeroDriftBrownian β l y t sample))^2 ∂canonicalBrownianMeasure) ≤
      2*m^2*Real.exp (2*|m| *β^2)*Real.exp (|y| *(2*|m|)+β^2*(T : ℝ)*(2*|m|)^2/2) := by
  let v := (β^2*(t : ℝ)).toNNReal
  have hY := hasLaw_zeroDriftBrownian β l y t
  have hi := (memLp_two_constantMassHeatCoefficient β μ s hs m l y t).integrable_norm_pow'
  have hG := integrable_exp_mul_abs_gaussian y (2*|m|) v (by positivity)
  have hmeas : Measurable (fun x => Real.exp (2*|m| *|x|)) := by fun_prop
  have hcomp := hY.integrable_comp hG
  have hh := integral_mono (by simpa only [Real.norm_eq_abs,sq_abs] using hi)
    ((hcomp.const_mul (m^2*Real.exp (2*|m| *β^2))))
    (fun sample => heat_coefficient_sq_pointwise β m μ s hs _)
  rw [integral_const_mul] at hh
  simp only [Function.comp_def] at hh
  have hiY := hY.integral_comp hmeas.aestronglyMeasurable
  simp only [Function.comp_def] at hiY
  rw [hiY] at hh
  have hv : (v : ℝ) ≤ β^2*(T : ℝ) := by
    dsimp [v]
    rw [max_eq_left (mul_nonneg (sq_nonneg β) t.coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (sq_nonneg β)
  have he := integral_exp_mul_abs_gaussian_le y (2*|m|) v (by positivity)
  have heT : Real.exp (|y| *(2*|m|)+(v : ℝ)*(2*|m|)^2/2) ≤
      Real.exp (|y| *(2*|m|)+β^2*(T : ℝ)*(2*|m|)^2/2) := by
    apply Real.exp_le_exp.mpr
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hv (sq_nonneg _)) (by norm_num))
  exact hh.trans (by
    have hhh := mul_le_mul_of_nonneg_left
      (he.trans (mul_le_mul_of_nonneg_left heT (by norm_num)))
      (show 0 ≤ m^2*Real.exp (2*|m| *β^2) by positivity)
    convert hhh using 1
    ring)

/-- Time--sample square integrability of the literal display-17
coefficient, including closed constant-CDF cell endpoints. -/
theorem integrable_constantMassHeatCoefficient_sq_prod (β : ℝ) (μ : ParisiMeasure)
    (m : ℝ) (l T : ℝ≥0) (hT : (l : ℝ)+(T : ℝ) ≤ 1) (y : ℝ) :
    Integrable (fun p : ℝ×BrownianSample =>
      (m*Real.exp (m*parisiPotential β μ ((l : ℝ)+p.1,
        zeroDriftBrownian β l y p.1.toNNReal p.2))*
          parisiGradient β μ ((l : ℝ)+p.1,
            zeroDriftBrownian β l y p.1.toNNReal p.2))^2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod canonicalBrownianMeasure) := by
  have hNN : Measurable (Function.uncurry (zeroDriftBrownian β l y)) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (continuous_zeroDriftBrownian β l y)
    intro t
    exact (((stronglyAdapted_zeroDriftBrownian β l y) t).measurable).mono
      ((canonicalBrownianShiftFiltration l).le t) le_rfl
  have hX : Measurable (fun p : ℝ×BrownianSample =>
      zeroDriftBrownian β l y p.1.toNNReal p.2) := by
    exact hNN.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable (fun p : ℝ×BrownianSample =>
      ((l : ℝ)+p.1,zeroDriftBrownian β l y p.1.toNNReal p.2)) :=
    (measurable_const.add measurable_fst).prodMk hX
  have hU := (continuous_parisiPotential β μ).measurable.comp hpair
  have hB := (continuous_parisiGradient β μ).measurable.comp hpair
  have hmeas := ((Real.measurable_exp.comp (hU.const_mul m)).const_mul m).mul hB |>.pow_const 2
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : (l : ℝ)+t ∈ Icc (0 : ℝ) 1 :=
    ⟨add_nonneg l.coe_nonneg ht.1,(add_le_add le_rfl ht.2).trans hT⟩
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hi := (memLp_two_constantMassHeatCoefficient β μ ((l : ℝ)+t)
      (hs t ht) m l y t.toNNReal).integrable_norm_pow'
    simpa only [Function.comp_def,Pi.mul_apply,Pi.pow_apply,Prod.fst,Prod.snd,
      Real.norm_eq_abs,sq_abs] using hi
  · let C := 2*m^2*Real.exp (2*|m| * β^2)*
      Real.exp (|y| * (2*|m|)+β^2*(T : ℝ)*(2*|m|)^2/2)
    have hC : Integrable (fun _ : ℝ => C) (volume.restrict (Icc (0 : ℝ) T)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    apply hC.mono' hmeas.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hsq (sample : BrownianSample) :
        ‖(m*Real.exp (m*parisiPotential β μ ((l : ℝ)+t,
          zeroDriftBrownian β l y t.toNNReal sample))*parisiGradient β μ
            ((l : ℝ)+t,zeroDriftBrownian β l y t.toNNReal sample))^2‖ =
        (m*Real.exp (m*parisiPotential β μ ((l : ℝ)+t,
          zeroDriftBrownian β l y t.toNNReal sample))*parisiGradient β μ
            ((l : ℝ)+t,zeroDriftBrownian β l y t.toNNReal sample))^2 :=
      Real.norm_of_nonneg (sq_nonneg _)
    rw [Real.norm_of_nonneg (integral_nonneg (fun sample => norm_nonneg _))]
    change (∫ sample, ‖(m*Real.exp (m*parisiPotential β μ ((l : ℝ)+t,
      zeroDriftBrownian β l y t.toNNReal sample))*parisiGradient β μ
        ((l : ℝ)+t,zeroDriftBrownian β l y t.toNNReal sample))^2‖ ∂canonicalBrownianMeasure) ≤ C
    simp only [hsq]
    exact integral_constantMassHeatCoefficient_sq_le β μ ((l : ℝ)+t)
      (hs t ht) m l y t.toNNReal T (by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2)

end FRSB
