module
public import FRSB.ItoStochasticTools
public import StochasticCalculus.TendstoInMeasureAlgebra

@[expose] public section

/-! A genuine diagonal passage for stochastic Riemann sums. It permits closing
an open-cell Itô formula at its endpoints without assuming endpoint temporal
smoothness. The inner mesh grows at least as fast as the outer crop index. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace FRSB

 theorem exists_diagonal_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : ℕ → ℕ → Ω → ℝ} {B : ℕ → Ω → ℝ} {C : Ω → ℝ}
    (hA : ∀n,TendstoInMeasure P (A n) atTop (B n))
    (hB : TendstoInMeasure P B atTop C) :
    ∃ k : ℕ → ℕ, (∀n,n≤k n) ∧
      TendstoInMeasure P (fun n => A n (k n)) atTop C := by
  let N := fun n => Classical.choose (MeasureTheory.ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (hA n) n)
  let k := fun n => max n (N n)
  have hk (n : ℕ) : n≤k n := le_max_left _ _
  have hb (n : ℕ) : P {ω | (2⁻¹:ℝ≥0∞)^n ≤ edist (A n (k n) ω) (B n ω)} ≤ (2⁻¹:ℝ≥0∞)^n :=
    Classical.choose_spec (MeasureTheory.ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (hA n) n) (k n) (le_max_right _ _)
  have herr : TendstoInMeasure P (fun n ω => A n (k n) ω-B n ω) atTop (fun _ => 0) := by
    intro ε hε
    rw [ENNReal.tendsto_atTop_zero]
    intro δ hδ
    obtain ⟨i,hi⟩ := ENNReal.exists_inv_two_pow_lt hε.ne'
    obtain ⟨j,hj⟩ := ENNReal.exists_inv_two_pow_lt hδ.ne'
    refine ⟨max i j,fun n hn => ?_⟩
    have hni : (2⁻¹:ℝ≥0∞)^n ≤ (2⁻¹:ℝ≥0∞)^i :=
      pow_le_pow_right_of_le_one' (by norm_num) ((le_max_left _ _).trans hn)
    have hnj : (2⁻¹:ℝ≥0∞)^n ≤ (2⁻¹:ℝ≥0∞)^j :=
      pow_le_pow_right_of_le_one' (by norm_num) ((le_max_right _ _).trans hn)
    apply le_trans (measure_mono (show {ω | ε ≤ edist (A n (k n) ω-B n ω) 0} ⊆
      {ω | (2⁻¹:ℝ≥0∞)^n ≤ edist (A n (k n) ω) (B n ω)} from ?_))
      ((hb n).trans (hnj.trans hj.le))
    intro ω hω
    change ε ≤ edist (A n (k n) ω-B n ω) 0 at hω
    change (2⁻¹:ℝ≥0∞)^n ≤ edist (A n (k n) ω) (B n ω)
    have he : edist (A n (k n) ω-B n ω) 0=edist (A n (k n) ω) (B n ω) := by
      simp only [edist_dist,dist_eq_norm_sub,sub_zero]
    rw [he] at hω
    exact (hni.trans hi.le).trans hω
  refine ⟨k,hk,?_⟩
  have hh := herr.add_real_noMeas hB
  simpa only [sub_add_cancel,zero_add] using hh

end FRSB
