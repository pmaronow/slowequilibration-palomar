-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNoiseL2

/-! Dimension-free Gaussian maximal correlation, derived from the genuine
complete product-Hermite Hilbert basis and the true Mehler noise law. -/
@[expose] public section
namespace SlowEquilibration.GaussianMaximalCorrelation
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {ι : Type*} [Fintype ι]

lemma hermite_coeff_eq_inner {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) (a : ι → ℕ) :
    coeff f a=inner ℝ (productHermiteBasis a) (hf.toLp f) := by
  have hBasis : productHermiteBasis a=psiVec a := by
    simp only [productHermiteBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [hBasis]
  exact (integral_inner_toLp (memLp_psi a) hf).symm

lemma hermite_hasSum_sq {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    HasSum (fun a => (coeff f a)^2) (∫ x,f x^2 ∂γpi ι) := by
  have hs:=productHermiteBasis.hasSum_inner_mul_inner (hf.toLp f) (hf.toLp f)
  have hc (a : ι → ℕ) : inner ℝ (hf.toLp f) (productHermiteBasis a)=coeff f a := by
    rw [real_inner_comm]
    exact (hermite_coeff_eq_inner hf a).symm
  simp only [hc,← hermite_coeff_eq_inner hf,← pow_two] at hs
  simpa only [integral_inner_toLp hf hf,← pow_two] using hs

lemma coeff_zero (f : (ι → ℝ) → ℝ) : coeff f 0=∫ x,f x ∂γpi ι := by
  simp [coeff,psi,H]

lemma degree_eq_zero_iff (a : ι → ℕ) : degree a=0 ↔ a=0 := by
  simp only [degree,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies,funext_iff,Pi.zero_apply]

/-- Actual L² contraction on the zero-mean subspace, for both signs of ρ. -/
theorem noise_centered_square_bound (ρ s : ℝ) (h : ρ^2+s^2=1) (hρ : |ρ| ≤ 1)
    {G : (ι → ℝ) → ℝ} (hG : Measurable G) (hG2 : MemLp G 2 (γpi ι))
    (hmean : ∫ x,G x ∂γpi ι=0) :
    (∫ x,noise ρ s G x^2 ∂γpi ι) ≤ ρ^2*(∫ x,G x^2 ∂γpi ι) := by
  have hN:=memLp_noise_L2 ρ s h hG hG2
  have hsq : ρ^2 ≤ 1 := by
    have hh:=(sq_le_sq₀ (abs_nonneg ρ) (by norm_num : 0 ≤ (1:ℝ))).mpr hρ
    simpa only [sq_abs,one_pow] using hh
  apply hasSum_le (fun a => ?_) (hermite_hasSum_sq hN) ((hermite_hasSum_sq hG2).mul_left (ρ^2))
  rw [noise_coefficient_L2 ρ s h hG hG2,mul_pow]
  by_cases ha : a=0
  · subst a
    rw [coeff_zero,hmean]
    simp
  · have hd : 1 ≤ degree a := Nat.one_le_iff_ne_zero.mpr (mt (degree_eq_zero_iff a).mp ha)
    have hp : (ρ^degree a)^2 ≤ ρ^2 := by
      rw [← pow_mul,Nat.mul_comm (degree a) 2,pow_mul]
      simpa only [pow_one] using pow_le_pow_of_le_one (sq_nonneg ρ) hsq hd
    exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)

lemma toLp_norm_sq {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    ‖hf.toLp f‖^2=∫ x,f x^2 ∂γpi ι := by
  rw [← real_inner_self_eq_norm_sq,integral_inner_toLp hf hf]
  simp only [← pow_two]

/-- Genuine Gebelein bound under the actual coupled product Gaussian law.
No desired correlation estimate, noise contraction or spectral gap is a premise. -/
theorem gaussian_maximal_correlation_centered (ρ s : ℝ) (h : ρ^2+s^2=1) (hρ : |ρ| ≤ 1)
    {F G : (ι → ℝ) → ℝ} (_hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 (γpi ι)) (hG2 : MemLp G 2 (γpi ι))
    (hGmean : ∫ x,G x ∂γpi ι=0) :
    |∫ z : (ι → ℝ)×(ι → ℝ),F z.1*G (ρ • z.1+s • z.2) ∂(γpi ι).prod (γpi ι)| ≤
      |ρ| * ‖hF2.toLp F‖*‖hG2.toLp G‖ := by
  have hN:=memLp_noise_L2 ρ s h hG hG2
  have hn : ‖hN.toLp (noise ρ s G)‖ ≤ |ρ| * ‖hG2.toLp G‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,sq_abs,toLp_norm_sq,toLp_norm_sq]
    exact noise_centered_square_bound ρ s h hρ hG hG2 hGmean
  have hi : Integrable (fun z : (ι → ℝ)×(ι → ℝ) => F z.1*G (ρ • z.1+s • z.2))
      ((γpi ι).prod (γpi ι)) := (hF2.comp_fst (γpi ι)).integrable_mul (coupled_memLp ρ s h hG2)
  rw [integral_prod _ hi]
  have heq : (fun x : ι → ℝ => ∫ y,F x*G (ρ • x+s • y) ∂γpi ι)=
      (fun x => F x*noise ρ s G x) := by funext x;exact integral_const_mul _ _
  rw [heq,← integral_inner_toLp hF2 hN]
  calc
    _ ≤ ‖hF2.toLp F‖*‖hN.toLp (noise ρ s G)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖hF2.toLp F‖*(|ρ| * ‖hG2.toLp G‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by ring

end
end SlowEquilibration.GaussianMaximalCorrelation
