module

public import SphericalAging.GaussianSmoothConcentration
public import SphericalAging.LipschitzBumpApproximation

public section

/-! Dimension-free concentration of an arbitrary finite-dimensional Gaussian
Lipschitz observable. Actual bump convolution and Gaussian dominated
convergence remove the smoothness assumption from the rotation proof. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianLipschitzConcentration
open Set Filter MeasureTheory ProbabilityTheory GaussianExponentialNorm GaussianSmoothConcentration
open scoped NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem centered_hasSubgaussianMGF (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x-∫y,f y ∂stdGaussian E)
      (rotationConstant L) (stdGaussian E) := by
  obtain ⟨g,hg,hLip,herror,hpoint,hderiv⟩ :=
    LipschitzBumpApproximation.exists_smooth_lipschitz_approximation
      (Measure.addHaar : Measure E) f hf
  have herror' (n : ℕ) (x : E) : |g n x-f x|≤(L:ℝ) := by
    have hh := herror n x
    rw [Real.dist_eq] at hh
    apply hh.trans
    exact (div_le_iff₀ (by positivity)).mpr (by
      have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
      nlinarith [L.coe_nonneg])
  have hfGrowth (x : E) : |f x|≤|f 0|+(L:ℝ)*‖x‖ := by
    have hl : |f x-f 0|≤(L:ℝ)*‖x‖ := by
      simpa only [Real.dist_eq,dist_zero_right] using hf.dist_le_mul x 0
    have hh := abs_add_le (f x-f 0) (f 0)
    rw [sub_add_cancel] at hh
    linarith
  have hgGrowth (n : ℕ) (x : E) : |g n x|≤|f 0|+(L:ℝ)+(L:ℝ)*‖x‖ := by
    have hh := abs_add_le (g n x-f x) (f x)
    rw [sub_add_cancel] at hh
    linarith [herror' n x,hfGrowth x]
  have hDom : Integrable (fun x : E => |f 0|+(L:ℝ)+(L:ℝ)*‖x‖) (stdGaussian E) :=
    (integrable_const _).add ((IsGaussian.integrable_id (μ:=stdGaussian E)).norm.const_mul _)
  have hmean : Tendsto (fun n => ∫x,g n x ∂stdGaussian E) atTop
      (𝓝 (∫x,f x ∂stdGaussian E)) :=
    tendsto_integral_of_dominated_convergence _
      (fun n => (hLip n).continuous.stronglyMeasurable.aestronglyMeasurable) hDom
      (fun n => ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hgGrowth n x))
      (ae_of_all _ hpoint)
  have hMGF (t : ℝ) : Tendsto (fun n => ∫x,Real.exp (t*g n x) ∂stdGaussian E) atTop
      (𝓝 (∫x,Real.exp (t*f x) ∂stdGaussian E)) := by
    have hExpDom := (integrable_exp_norm (stdGaussian E) (|t| * (L:ℝ))).const_mul
      (Real.exp (|t| * (|f 0|+(L:ℝ))))
    apply tendsto_integral_of_dominated_convergence _
      (fun n => ((hLip n).continuous.measurable.const_mul t).exp.aestronglyMeasurable) hExpDom
    · intro n
      exact ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (Real.exp_nonneg _),←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have ht := mul_le_mul_of_nonneg_left (hgGrowth n x) (abs_nonneg t)
        have hh := le_abs_self (t*g n x)
        rw [abs_mul] at hh
        nlinarith)
    · exact ae_of_all _ (fun x => Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x:=t)).mul (hpoint x)))
  have hcenter (t : ℝ) : Tendsto
      (fun n => mgf (fun x => g n x-∫y,g n y ∂stdGaussian E) (stdGaussian E) t)
      atTop (𝓝 (mgf (fun x => f x-∫y,f y ∂stdGaussian E) (stdGaussian E) t)) := by
    have he (u : E→ℝ) : mgf (fun x => u x-∫y,u y ∂stdGaussian E) (stdGaussian E) t =
        Real.exp (-t*(∫y,u y ∂stdGaussian E))*(∫x,Real.exp (t*u x) ∂stdGaussian E) := by
      unfold mgf
      rw [←integral_const_mul]
      congr 1
      funext x
      rw [←Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    exact (Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x:=-t)).mul hmean)).mul (hMGF t)
  refine ⟨fun t => ?_,fun t => ?_⟩
  · have hi := (integrable_exp_lipschitz (stdGaussian E) f hf t).const_mul
      (Real.exp (-t*(∫y,f y ∂stdGaussian E)))
    convert hi using 1
    funext x
    rw [←Real.exp_add]
    congr 1
    ring
  · apply le_of_tendsto (hcenter t)
    exact Eventually.of_forall (fun n =>
      (GaussianSmoothConcentration.centered_hasSubgaussianMGF (g n)
        ((hg n).of_le (by simp)) L (hderiv n)).mgf_le t)

theorem centered_absolute_tail (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (ε : ℝ) (hε : 0≤ε) :
    (stdGaussian E).real {x | ε≤|f x-∫y,f y ∂stdGaussian E|}≤
      2*Real.exp (-ε^2/(2*(rotationConstant L:ℝ))) := by
  let X : E→ℝ := fun x => f x-∫y,f y ∂stdGaussian E
  have hG := centered_hasSubgaussianMGF f hf
  have hs : {x | ε≤|X x|}={x | ε≤X x}∪{x | ε≤-X x} := by
    ext x
    change ε≤|X x| ↔ ε≤X x ∨ ε≤-X x
    exact le_abs
  change (stdGaussian E).real {x | ε≤|X x|}≤_
  rw [hs]
  have hn := hG.neg.measure_ge_le hε
  have hp := hG.measure_ge_le hε
  exact (measureReal_union_le _ _).trans
    (by simpa only [two_mul,Pi.neg_apply] using add_le_add hp hn)

end SphericalAging.GaussianLipschitzConcentration
