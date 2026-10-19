-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionFailureRates
public import SlowEquilibration.GOEEdgePolynomialRate

/-! Genuine exponential control of the literal determinant-weight selection
loss and its absorption into the printed retained-pair normalization. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Filter SphericalModel SphericalGaussianJet
open scoped Topology
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem sourceSelectionWeightError_exponential (C₂ : ℝ) (hC₂ : 0 < C₂)
    (μ : FiniteMixture) {Q G g : ℝ} (hQ : 0 < Q) (hG : 0 < G) (hg : 0 < g) (grid : ℕ) :
    ∃ A c : ℝ,0 < A ∧ 0 < c ∧ ∀ n : ℕ,
      sourceSelectionWeightError C₂ μ Q G g grid n ≤ A*Real.exp (-c*(n+2:ℕ)) := by
  let cH := ((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2)
  let cB := (G/8)^2/(2*μ.xi Q)
  have hcH : 0 < cH := by
    have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
    dsimp only [cH]
    positivity
  have hcB : 0 < cB := by
    have hξ := μ.xi_pos hQ
    dsimp only [cB]
    positivity
  let d := min (1/2:ℝ) (min cH cB)
  let K := 2*(Fintype.card (Degree μ.maxDegree):ℝ)+Real.exp cH+(grid+1:ℕ)
  have hd : 0 < d := lt_min (by norm_num) (lt_min hcH hcB)
  have hK : 0 < K := by dsimp only [K];positivity
  have hd0 : d ≤ 1/2 := min_le_left _ _
  have hdH : d ≤ cH := (min_le_right _ _).trans (min_le_left _ _)
  have hdB : d ≤ cB := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Real.sqrt C₂*Real.sqrt K,d/2,by positivity,by positivity,?_⟩
  intro n
  have hN : 0 ≤ ((n+2:ℕ):ℝ) := by positivity
  have h0 : Real.exp (-((n+2:ℕ):ℝ)/2) ≤ Real.exp (-d*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hd0 hN]
  have hH : Real.exp (-(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2)) ≤
      Real.exp cH*Real.exp (-d*(n+2:ℕ)) := by
    have he : -(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2) =
        cH-cH*(n+2:ℕ) := by dsimp only [cH];push_cast;ring
    rw [he,Real.exp_sub]
    have hE : Real.exp (-cH*(n+2:ℕ)) ≤ Real.exp (-d*(n+2:ℕ)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hdH hN])
    have he' : Real.exp (cH-cH*(n+2:ℕ))=Real.exp cH*Real.exp (-cH*(n+2:ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← Real.exp_sub,he']
    exact mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
  have hB : Real.exp (-(n+2:ℕ)*(G/8)^2/(2*μ.xi Q)) ≤ Real.exp (-d*(n+2:ℕ)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hdB hN
    dsimp only [cB] at hh
    convert neg_le_neg hh using 1 <;> ring
  have hRate : sourceSelectionFailureRate μ Q G g grid n ≤ K*Real.exp (-d*(n+2:ℕ)) := by
    unfold sourceSelectionFailureRate
    exact (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left h0 (by positivity)) hH)
      (mul_le_mul_of_nonneg_left hB (by positivity))).trans_eq (by dsimp only [K];ring)
  calc
    sourceSelectionWeightError C₂ μ Q G g grid n ≤ Real.sqrt C₂*Real.sqrt (K*Real.exp (-d*(n+2:ℕ))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRate) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hK.le,GOEEdgePolynomialRate.sqrt_exp_eq]
      rw [show -d*((n+2:ℕ):ℝ)/2=-(d/2)*(n+2:ℕ) by ring]
      ring

theorem sourceSelectionWeightError_shifted_le_inverse_sqrt_eventually (C₂ : ℝ) (hC₂ : 0 < C₂)
    (μ : FiniteMixture) {Q G g : ℝ} (hQ : 0 < Q) (hG : 0 < G) (hg : 0 < g) (grid : ℕ) :
    ∀ᶠ n : ℕ in atTop,sourceSelectionWeightError C₂ μ Q G g grid (n+1) ≤ 1/Real.sqrt (n+3:ℕ) := by
  obtain ⟨A,c,hA,hc,hRate⟩ := sourceSelectionWeightError_exponential C₂ hC₂ μ hQ hG hg grid
  have hlarge : ∀ᶠ n : ℕ in atTop,(A/c)^2 ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((A/c)^2))
  filter_upwards [hlarge] with n hn
  have hN : 0 < ((n+3:ℕ):ℝ) := by positivity
  have hS : 0 < Real.sqrt (n+3:ℕ) := Real.sqrt_pos.mpr hN
  have hdim : (A/c)^2 ≤ ((n+3:ℕ):ℝ) := hn.trans (by push_cast;linarith)
  have hroot : A/c ≤ Real.sqrt (n+3:ℕ) := (Real.le_sqrt (by positivity) hN.le).mpr hdim
  have hE : A*Real.exp (-c*(n+3:ℕ)) ≤ (A/c)/(n+3:ℕ) := by
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ hc).mpr
    have he := (Real.mul_exp_neg_le_exp_neg_one (c*(n+3:ℕ))).trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-1:ℝ) ≤ 0))
    calc
      _ = A*(c*(n+3:ℕ)*Real.exp (-(c*(n+3:ℕ)))) := by ring
      _ ≤ A*1 := mul_le_mul_of_nonneg_left he hA.le
      _ = A := by ring
  have hLast : (A/c)/(n+3:ℕ) ≤ 1/Real.sqrt (n+3:ℕ) := by
    apply (div_le_div_iff₀ hN hS).mpr
    have hh := mul_le_mul_of_nonneg_right hroot hS.le
    simpa only [← pow_two,Real.sq_sqrt hN.le,one_mul] using hh
  have hh := hRate (n+1)
  simpa only [show n+1+2=n+3 by omega] using hh.trans (hE.trans hLast)

theorem retained_normalization_absorption {C p t : ℝ} (hC : 0 ≤ C)
    (hp : p ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 (1/2)) (htp : t ≤ p) :
    (1+C*p)/(1-t)^2 ≤ 1+(9*C+8)*p := by
  rcases hp with ⟨hp0,hp1⟩
  rcases ht with ⟨ht0,ht1⟩
  have hden : 0 < (1-t)^2 := sq_pos_of_pos (by linarith : 0 < 1-t)
  have hden4 : 1/4 ≤ (1-t)^2 := by nlinarith [sq_nonneg (t-1/2)]
  have hbase : 1/(1-t)^2 ≤ 1+8*t := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hden4 (show 0 ≤ 8*t by positivity)
    nlinarith [sq_nonneg t]
  have hnum : 0 ≤ 1+C*p := by positivity
  have hp2 : p^2 ≤ p := by nlinarith [mul_le_mul_of_nonneg_left hp1 hp0]
  calc
    _ = (1+C*p)*(1/(1-t)^2) := by ring
    _ ≤ (1+C*p)*(1+8*t) := mul_le_mul_of_nonneg_left hbase hnum
    _ ≤ (1+C*p)*(1+8*p) := mul_le_mul_of_nonneg_left (by linarith) hnum
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 8*C by positivity)]

end
end SlowEquilibration.PairConditionalDeterminantMoments
