module
public import FRSB.BackwardHeatQuotient
public import FRSB.ForwardExponentialBounds
public import FRSB.UniformSpatialRegularity

@[expose] public section

/-! Genuine exponentially growing terminal data for the bounded backward
Fourier tests. All hypotheses are discharged for the selected PDE potential. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology ContDiff BigOperators
namespace FRSB
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

lemma hasExpGrowth_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, HasExpGrowth (f i)) : HasExpGrowth (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasExpGrowth.const 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem HeatC2Datum.mul {F G : ℝ → ℝ} (hF : HeatC2Datum F) (hG : HeatC2Datum G) :
    HeatC2Datum (fun x => F x * G x) := by
  refine ⟨hF.smooth.mul hG.smooth, fun j hj => ?_⟩
  have he : iteratedDeriv j (fun x => F x * G x) =
      fun x => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        iteratedDeriv i F x * iteratedDeriv (j - i) G x := by
    funext x
    exact iteratedDeriv_mul (hF.smooth.of_le (by exact_mod_cast hj)).contDiffAt
      (hG.smooth.of_le (by exact_mod_cast hj)).contDiffAt
  rw [he]
  apply hasExpGrowth_finset_sum
  intro i hi
  have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  exact ((hF.growth i (hij.trans hj)).const_mul (j.choose i : ℝ)).mul
    (hG.growth (j - i) ((Nat.sub_le _ _).trans hj))

theorem heatC2Datum_cos (ξ : ℝ) : HeatC2Datum (fun x => Real.cos (ξ * x)) := by
  refine ⟨Real.contDiff_cos.comp (contDiff_const.mul contDiff_id), fun j _ => ?_⟩
  apply HasExpGrowth.of_bounded (C := |ξ| ^ j)
  intro x
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos ξ, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg ξ) j)
    (Real.abs_iteratedDeriv_cos_le_one j (ξ * x))

theorem heatC2Datum_sin (ξ : ℝ) : HeatC2Datum (fun x => Real.sin (ξ * x)) := by
  refine ⟨Real.contDiff_sin.comp (contDiff_const.mul contDiff_id), fun j _ => ?_⟩
  apply HasExpGrowth.of_bounded (C := |ξ| ^ j)
  intro x
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sin ξ, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg ξ) j)
    (Real.abs_iteratedDeriv_sin_le_one j (ξ * x))

theorem heatC2Datum_exp_parisiPotential (β : ℝ) (μ : ParisiMeasure) (b m : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1) :
    HeatC2Datum (fun x => Real.exp (m * parisiPotential β μ (b, x))) := by
  let A := fun x => parisiPotential β μ (b, x)
  have hA : ContDiff ℝ ∞ A := contDiff_parisiPotential_spatial β μ b hb
  have hD : HasExpGrowth (fun x => Real.exp (m * A x)) :=
    (parisiPotential_hasLinearGrowth β μ b hb).exp_mul m
  refine ⟨((contDiff_const.mul hA).exp).of_le (by simp), fun j _ => ?_⟩
  let K := fun n => uniformSpatialConstant β (n - 1)
  have hK : ∀ n, 0 ≤ K n := fun n => (uniformSpatialConstant_pos β (n - 1)).le
  have hAn : ∀ n x, ‖iteratedDeriv (n + 1) (fun y => -A y) x‖ ≤ K (n + 1) := by
    intro n x
    simp only [iteratedDeriv_fun_neg, norm_neg, K, Nat.add_sub_cancel]
    rw [← parisiSpatialField_eq_iteratedDeriv β μ (n + 1) b x hb]
    exact parisiSpatialField_uniform_bound β n μ (b, x)
  have hh := norm_iteratedDeriv_exp_neg_mul_le (fun y => -A y) m hA.neg hm K hK hAn j
  obtain ⟨C, c, hc, hbound⟩ := hD
  simp only [abs_of_pos (Real.exp_pos _)] at hbound
  refine ⟨exponentialDerivativeConstant K j * C, c, hc, fun x => ?_⟩
  have hhx := hh x
  simp only [neg_mul_neg, Real.norm_eq_abs] at hhx
  exact hhx.trans (by
    calc
      _ ≤ exponentialDerivativeConstant K j * (C * Real.exp (c * |x|)) :=
        mul_le_mul_of_nonneg_left (hbound x) (exponentialDerivativeConstant_nonneg K hK j)
      _ = _ := by ring)

theorem heatC2Datum_parisiCos (β : ℝ) (μ : ParisiMeasure) (b m ξ : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1) :
    HeatC2Datum (fun x => Real.exp (m * parisiPotential β μ (b, x)) * Real.cos (ξ * x)) :=
  (heatC2Datum_exp_parisiPotential β μ b m hb hm).mul (heatC2Datum_cos ξ)

theorem heatC2Datum_parisiSin (β : ℝ) (μ : ParisiMeasure) (b m ξ : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1) :
    HeatC2Datum (fun x => Real.exp (m * parisiPotential β μ (b, x)) * Real.sin (ξ * x)) :=
  (heatC2Datum_exp_parisiPotential β μ b m hb hm).mul (heatC2Datum_sin ξ)

end FRSB
