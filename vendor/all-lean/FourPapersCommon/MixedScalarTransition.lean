module
public import FourPapersCommon.MixedColeHopf
public import FRSB.ConstantMassLaw

@[expose] public section

/-! Actual normalized scalar transition kernels for mixed Parisi cells.
The endpoint potential and variance increment are the literal mixed objects;
zero masses and zero elapsed variances remain genuine probability kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000

def mixedScalarTransition (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (a b m : ℝ) : Kernel ℝ ℝ :=
  FRSB.constantMassKernel m (ξ.first b - ξ.first a).toNNReal
    (fun y => mixedPotential ξ μ (b, y))

theorem continuous_mixedPotential_section (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (b : ℝ) : Continuous (fun y => mixedPotential ξ μ (b, y)) := by
  change Continuous (fun y => Paper.parisiPotential (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock b, y))
  exact (Paper.continuous_parisiPotential (mixedBeta ξ) (mixedMeasure ξ μ)).comp
    (continuous_const.prodMk continuous_id)

theorem mixedPotential_hasLinearGrowth (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    HasLinearGrowth (fun y => mixedPotential ξ μ (b, y)) :=
  FRSB.parisiPotential_hasLinearGrowth (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock b)
    (ξ.clock_mem_unitInterval hb)

theorem isMarkovKernel_mixedScalarTransition (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    (a b m : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) : IsMarkovKernel (mixedScalarTransition ξ μ a b m) :=
  FRSB.isMarkovKernel_constantMassKernel m _ _ (continuous_mixedPotential_section ξ μ b)
    (mixedPotential_hasLinearGrowth ξ μ hb)

theorem mixedScalarTransition_apply_actual (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hc : ∀ q ∈ Ico a b, Paper.parisiCDF μ q = m) (x : ℝ) :
    mixedScalarTransition ξ μ a b m x =
      (gaussianReal x (ξ.first b - ξ.first a).toNNReal).withDensity
        (fun y => ENNReal.ofReal (Real.exp (m *
          (mixedPotential ξ μ (b, y) - mixedPotential ξ μ (a, x))))) := by
  rw [mixedScalarTransition, FRSB.constantMassKernel_apply m _ _
    (continuous_mixedPotential_section ξ μ b) (mixedPotential_hasLinearGrowth ξ μ hb)]
  simp only [FRSB.constantMassTransition, FRSB.constantMassWeight,
    ← mixedPotential_coleHopf_on_constantCDF ξ μ ha hb hab hc x]

private theorem hasDerivAt_coleHopf_kernel_average {A A' : ℝ → ℝ}
    (hA : ∀ y, HasDerivAt A (A' y) y) (hAg : HasLinearGrowth A)
    (hAc : Continuous A) (hA'm : Measurable A') (hA'b : ∀ y, |A' y| ≤ 1)
    (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (coleHopf m v A) (∫ y, A' y ∂FRSB.constantMassKernel m v A x) x := by
  have hA'g : HasExpGrowth A' := HasExpGrowth.of_bounded hA'b
  have he : (∫ y, A' y ∂FRSB.constantMassKernel m v A x) =
      ∫ z, A' (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v := by
    rw [FRSB.integral_constantMassKernel m v A hAc hAg]
    have hshift : (gaussianReal 0 v).map (fun z => x + z) = gaussianReal x v := by
      simpa using (gaussianReal_map_const_add (μ := 0) (v := v) x)
    have hwm : Measurable (fun y => FRSB.constantMassWeight m v A x y) := by
      unfold FRSB.constantMassWeight
      fun_prop
    have hfm : Measurable (fun y => A' y * FRSB.constantMassWeight m v A x y) := hA'm.mul hwm
    rw [← hshift, integral_map (φ := fun z => x + z)
      (f := fun y => A' y * FRSB.constantMassWeight m v A x y) (by fun_prop) hfm.aestronglyMeasurable]
    rfl
  rw [he]
  by_cases hm : m = 0
  · subst m
    have hefun : coleHopf 0 v A = (fun y => ∫ z, A (y + z) ∂gaussianReal 0 v) :=
      funext (coleHopf_zero v A)
    rw [hefun]
    simp only [coleHopfQ_zero, mul_one]
    exact hasDerivAt_integral_comp_add_gaussianReal hA hAg.toHasExpGrowth hA'g hA'm 0 v x
  · exact hasDerivAt_coleHopf hA hAg hA'g hA'm hm v x

theorem mixedGradient_eq_transition_average (ξ : AdmissibleEvenMixture) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hc : ∀ q ∈ Ico a b, Paper.parisiCDF μ q = m) (x : ℝ) :
    mixedGradient ξ μ (a, x) =
      ∫ y, mixedGradient ξ μ (b, y) ∂mixedScalarTransition ξ μ a b m x := by
  have hgrad : Measurable (fun y => mixedGradient ξ μ (b, y)) := by
    change Measurable (fun y => Paper.parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ) (ξ.clock b, y))
    exact ((Paper.continuous_parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ)).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hd := hasDerivAt_coleHopf_kernel_average
    (fun y => hasDerivAt_mixedPotential_spatial ξ μ b y hb)
    (mixedPotential_hasLinearGrowth ξ μ hb) (continuous_mixedPotential_section ξ μ b) hgrad
    (fun y => by simpa only [Real.norm_eq_abs] using norm_mixedGradient_le_one ξ μ (b, y))
    m (ξ.first b - ξ.first a).toNNReal x
  have he : (fun y => mixedPotential ξ μ (a, y)) =
      coleHopf m (ξ.first b - ξ.first a).toNNReal (fun y => mixedPotential ξ μ (b, y)) :=
    funext (mixedPotential_coleHopf_on_constantCDF ξ μ ha hb hab hc)
  rw [← he] at hd
  exact (hasDerivAt_mixedPotential_spatial ξ μ a x ha).unique hd

end FourPapersCommon
