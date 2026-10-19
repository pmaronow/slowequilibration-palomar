-- SPDX-License-Identifier: Apache-2.0
module

public import FourPapersCommon.GaussianL2Limit
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! Actual Gaussian series with summable L² norms: the pointwise series is
identified almost everywhere with its genuine Hilbert-space sum, and its
Gaussian law is derived by the proved L² limit theorem. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianSummableSeries
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- The literal pointwise Gaussian series is Gaussian whenever its genuine
finite partial sums are Gaussian and its L² norms are absolutely summable. -/
theorem hasGaussianLaw_tsum {X : ℕ → Ω → E}
    (hX : ∀ n,MemLp (X n) 2 P)
    (hs : Summable (fun n => ‖(hX n).toLp (X n)‖))
    (hG : ∀ n,HasGaussianLaw (fun ω => ∑ k∈Finset.range n,X k ω) P) :
    HasGaussianLaw (fun ω => ∑' n,X n ω) P := by
  let Z : ℕ → Lp E 2 P := fun n => (hX n).toLp (X n)
  have hZ : Summable Z := hs.of_norm
  have hen : ∑' n,‖Z n‖ₑ≠⊤ := by
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs)
  have hcoe : ∀ᵐ ω ∂P,∀ n,Z n ω=X n ω := by
    rw [ae_all_iff]
    exact fun n => (hX n).coeFn_toLp
  have hg (n : ℕ) : HasGaussianLaw (∑ k∈Finset.range n,Z k : Lp E 2 P) P := by
    apply (hG n).congr
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) Z,hcoe] with ω hω he
    rw [hω]
    exact Finset.sum_congr rfl (fun k _ => (he k).symm)
  have hsum : HasGaussianLaw (∑' n,Z n : Lp E 2 P) P :=
    FourPapersCommon.hasGaussianLaw_of_L2_tendsto hg hZ.tendsto_sum_tsum_nat
  apply hsum.congr
  filter_upwards [Lp.coeFn_tsum hen,hcoe] with ω hω he
  rw [hω]
  exact tsum_congr (fun n => he n)

/-- Absolute convergence almost everywhere, from genuine L² summability. -/
theorem hasSum_tsum_ae {X : ℕ → Ω → E}
    (hX : ∀ n,MemLp (X n) 2 P)
    (hs : Summable (fun n => ‖(hX n).toLp (X n)‖)) :
    ∀ᵐ ω ∂P,HasSum (fun n => X n ω) (∑' n,X n ω) := by
  let Z : ℕ → Lp E 2 P := fun n => (hX n).toLp (X n)
  have hen : ∑' n,‖Z n‖ₑ≠⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs)
  have hc : ∀ᵐ ω ∂P,∀ n,Z n ω=X n ω := by
    rw [ae_all_iff]
    exact fun n => (hX n).coeFn_toLp
  filter_upwards [Lp.hasSum_coeFn_tsum hen,hc] with ω hω he
  have hh : HasSum (fun n => X n ω) ((∑' n,Z n) ω) := by
    simpa only [show (fun n => Z n ω)=(fun n => X n ω) from funext he] using hω
  exact hh.summable.hasSum

end SlowEquilibration.GaussianSummableSeries
