module

public import SphericalAging.GaussianOrthogonalForkCovariance
public import Mathlib.Probability.Moments.SubGaussian

public section

/-! Genuine Gaussian Chernoff bounds from the actual law and a computed
variance, including a finite union bound. No tail premise is required. -/
noncomputable section
namespace SphericalAging.CenteredGaussianConcentration
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem hasSubgaussianMGF_of_gaussian (X : Ω→ℝ) (hX : HasGaussianLaw X μ)
    (hm : ∫ω,X ω ∂μ=0) (c : ℝ≥0) (hv : variance X μ≤c) :
    HasSubgaussianMGF X c μ := by
  have hl : HasLaw X (gaussianReal 0 (variance X μ).toNNReal) μ :=
    ⟨hX.aemeasurable,by simpa only [hm] using hX.map_eq_gaussianReal⟩
  refine ⟨fun t => hl.integrable_fun_comp (integrable_exp_mul_gaussianReal t),?_⟩
  intro t
  rw [mgf_gaussianReal hl,zero_mul,zero_add]
  apply Real.exp_le_exp.mpr
  rw [Real.coe_toNNReal _ (variance_nonneg X μ)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (sq_nonneg t)) (by norm_num)

theorem gaussian_right_tail (X : Ω→ℝ) (hX : HasGaussianLaw X μ)
    (hm : ∫ω,X ω ∂μ=0) (c : ℝ≥0) (hv : variance X μ≤c)
    (ε : ℝ) (hε : 0≤ε) : μ.real {ω | ε≤X ω}≤Real.exp (-ε^2/(2*c)) :=
  (hasSubgaussianMGF_of_gaussian X hX hm c hv).measure_ge_le hε

theorem gaussian_absolute_tail (X : Ω→ℝ) (hX : HasGaussianLaw X μ)
    (hm : ∫ω,X ω ∂μ=0) (c : ℝ≥0) (hv : variance X μ≤c)
    (ε : ℝ) (hε : 0≤ε) : μ.real {ω | ε≤|X ω|}≤2*Real.exp (-ε^2/(2*c)) := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hs : {ω | ε≤|X ω|}={ω | ε≤X ω}∪{ω | ε≤-X ω} := by
    ext ω
    change ε≤|X ω| ↔ ε≤X ω ∨ ε≤-X ω
    exact le_abs
  have hG := hasSubgaussianMGF_of_gaussian X hX hm c hv
  rw [hs]
  have hn := hG.neg.measure_ge_le hε
  have hp := hG.measure_ge_le hε
  exact (measureReal_union_le _ _).trans (by simpa only [two_mul,Pi.neg_apply] using add_le_add hp hn)

theorem finite_gaussian_absolute_tail {ι : Type*} [Fintype ι] [IsFiniteMeasure μ]
    (X : ι→Ω→ℝ) (hX : ∀i,HasGaussianLaw (X i) μ)
    (hm : ∀i,∫ω,X i ω ∂μ=0) (c : ℝ≥0) (hv : ∀i,variance (X i) μ≤c)
    (ε : ℝ) (hε : 0≤ε) :
    μ.real {ω | ∃i,ε≤|X i ω|}≤(Fintype.card ι:ℝ)*2*Real.exp (-ε^2/(2*c)) := by
  classical
  have hs : {ω | ∃i,ε≤|X i ω|}=⋃i,{ω | ε≤|X i ω|} := by ext ω;simp
  rw [hs]
  calc
    _≤∑i,μ.real {ω | ε≤|X i ω|} := measureReal_iUnion_fintype_le _
    _≤∑_i : ι,2*Real.exp (-ε^2/(2*c)) :=
      Finset.sum_le_sum (fun i _ => gaussian_absolute_tail (X i) (hX i) (hm i) c (hv i) ε hε)
    _=_ := by simp [mul_assoc]

end SphericalAging.CenteredGaussianConcentration

namespace SphericalAging.GaussianOrthogonalForkConcentration
open MeasureTheory ProbabilityTheory FiniteModel GaussianOrthogonalForkCovariance CenteredGaussianConcentration
open scoped NNReal

theorem orthogonal_fork_absolute_tail {N p K : ℕ} (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (x : Vector N) (y : Fin K→Vector N) (r q : ℝ)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) (hf : OrthogonalFork x y r q)
    (ε : ℝ) (hε : 0≤ε) :
    (forkLaw N p K).real {J | ε≤|averagedIncrement a b x y J|}≤
      2*Real.exp (-(K:ℝ)*N*ε^2/2) := by
  let c : ℝ≥0 := ⟨1/((K:ℝ)*N),by positivity⟩
  have hc := gaussian_absolute_tail (averagedIncrement (p := p) a b x y)
    (averagedIncrement_hasGaussianLaw a b x y) (averagedIncrement_mean a b x y) c
    (orthogonal_fork_variance_le hN hp hK a b ha hab hb x y r q hr hq hq1 hf) ε hε
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  have he : -ε^2/(2*(c:ℝ))=-(K:ℝ)*N*ε^2/2 := by
    change -ε^2/(2*(1/((K:ℝ)*N)))=-(K:ℝ)*N*ε^2/2
    field_simp [hn,hk]
    <;> ring
  simpa only [he] using hc

end SphericalAging.GaussianOrthogonalForkConcentration
