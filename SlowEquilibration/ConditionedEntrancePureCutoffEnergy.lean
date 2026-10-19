-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceCutoffEnergyBound
public import SlowEquilibration.ConditionedEntrancePureSmoothCutoff
public import SlowEquilibration.EntranceLatitudePureSourceCorrectionBound

/-! Lowest-degree energy control for the proper pure value/tangent cutoff.
This uses the homogeneous pure correction, not the singular two-score row. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging HardSphereDynamics
open EntranceLatitudeTangentObservable
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem pure_cutoff_scalar_energy_bound
    (p : ℕ) (hp : 1 ≤ p)
    (n M R α r g X L : ℝ)
    (hn : 0 < n) (hM : 0 ≤ M) (hR : 0 ≤ R) (hα : 0 < α)
    (hL : 0 ≤ L) (hX : |X| ≤ M*n)
    (χ : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hχB : ∀ s, |χ s| ≤ B)
    (hχR : ∀ s, R < |s| → χ s = 0) :
    |χ (r/α)*χ (g/(n*α))*(L*(X*r^p-r^(p-1)*g))| ≤
      B^2*L*(M+1)*R^p*n*α^p := by
  by_cases h1 : χ (r/α) = 0
  · rw [h1,zero_mul,zero_mul,abs_zero]
    positivity
  by_cases h2 : χ (g/(n*α)) = 0
  · rw [h2,mul_zero,zero_mul,abs_zero]
    positivity
  have hRa : 0 ≤ R*α := mul_nonneg hR hα.le
  have hrα : |r| ≤ R*α := by
    have H := cutoff_support_argument_bound χ hχR h1
    rw [abs_div,abs_of_pos hα] at H
    exact (div_le_iff₀ hα).mp H
  have hgα : |g| ≤ n*(R*α) := by
    have H := cutoff_support_argument_bound χ hχR h2
    rw [abs_div,abs_of_pos (mul_pos hn hα)] at H
    have H' := (div_le_iff₀ (mul_pos hn hα)).mp H
    nlinarith [H']
  have hpow : |r|^p ≤ (R*α)^p :=
    pow_le_pow_left₀ (abs_nonneg r) hrα _
  have hpow1 : |r|^(p-1) ≤ (R*α)^(p-1) :=
    pow_le_pow_left₀ (abs_nonneg r) hrα _
  have he : (R*α)^(p-1)*(R*α) = (R*α)^p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hdelta : |L*(X*r^p-r^(p-1)*g)| ≤
      L*(M+1)*n*(R*α)^p := by
    rw [abs_mul,abs_of_nonneg hL]
    calc
      L * |X*r^p-r^(p-1)*g| ≤ L*((M+1)*n*(R*α)^p) :=
        mul_le_mul_of_nonneg_left (by
          calc
            |X*r^p-r^(p-1)*g| ≤ |X*r^p|+|r^(p-1)*g| := by
              simpa only [sub_zero,zero_sub,abs_neg] using
                abs_sub_le (X*r^p) 0 (r^(p-1)*g)
            _ = |X| * |r|^p+|r|^(p-1) * |g| := by
              simp only [abs_mul,abs_pow]
            _ ≤ (M*n)*(R*α)^p+(R*α)^(p-1)*(n*(R*α)) := by
              apply add_le_add
              · exact mul_le_mul hX hpow (pow_nonneg (abs_nonneg r) _)
                  (mul_nonneg hM hn.le)
              · exact mul_le_mul hpow1 hgα (abs_nonneg g)
                  (pow_nonneg hRa _)
            _ = (M+1)*n*(R*α)^p := by
              calc
                _ = (M*n)*(R*α)^p+n*((R*α)^(p-1)*(R*α)) := by ring
                _ = _ := by rw [he]; ring) hL
      _ = L*(M+1)*n*(R*α)^p := by ring
  rw [abs_mul,abs_mul]
  calc
    |χ (r/α)| * |χ (g/(n*α))| * |L*(X*r^p-r^(p-1)*g)| ≤
        (B*B)*(L*(M+1)*n*(R*α)^p) := by
      apply mul_le_mul
      · exact mul_le_mul (hχB _) (hχB _) (abs_nonneg _) hB
      · exact hdelta
      · exact abs_nonneg _
      · positivity
    _ = B^2*L*(M+1)*R^p*n*α^p := by rw [mul_pow]; ring

/-- On the original tensor-regularity event, the proper pure cutoff energy
differs from the original Hamiltonian by at most a model-only constant times
`N α^p`, uniformly in the conditioned axis and bounded value mark. -/
theorem regular_pure_source_cutoff_energy_difference
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B α : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hα : 0 < α)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder)
    (u x : Vector (n+1)) (hu : OnSphere u)
    (_hx : OnSphere x) (e : ℝ) (he : |e| ≤ B)
    (χ : ℝ → ℝ) (hχb : ∀ s, |χ s| ≤ 1)
    (hχR : ∀ s, 2 < |s| → χ s = 0) :
    let μ := FiniteMixture.pure p hp c hc
    let K := sourceLatitudeCenterConstant μ Q
    let L := ((Real.sqrt Q)^p)⁻¹
    |pureSourceSmoothCutoffField p hp c hc Q J u e α χ x-
      fieldOfMixture μ J x| ≤
      L*(B+K+1)*2^p*((n+1 : ℕ) : ℝ)*α^p := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let K := sourceLatitudeCenterConstant μ Q
  let L := ((Real.sqrt Q)^p)⁻¹
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let Hq := field (centerCoefficients (mixtureCoefficients μ) Q) J u
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  let r := overlap x u
  let g := inner ℝ G x
  have hN : 0 < N := by dsimp only [N]; positivity
  have hK : 0 ≤ K :=
    (derivativeConstant_pos (centerCoefficients (mixtureCoefficients μ) Q)).le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hHq : |Hq| ≤ K*N :=
    (source_latitude_center_observations μ Q J hJ u
      ((onSphere_iff_norm_sq u).mp hu)).1
  have hX : |N*e-Hq| ≤ (B+K)*N := by
    calc
      |N*e-Hq| ≤ |N*e|+|Hq| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (N*e) 0 Hq
      _ ≤ N*B+K*N := by
        rw [abs_mul,abs_of_pos hN]
        exact add_le_add (mul_le_mul_of_nonneg_left he hN.le) hHq
      _ = (B+K)*N := by ring
  have hscalar := pure_cutoff_scalar_energy_bound p (by omega : 1 ≤ p)
    N (B+K) 2 α r g (N*e-Hq) L hN (add_nonneg hB hK)
    (by norm_num) hα hL hX χ (B := 1) (by norm_num) hχb hχR
  unfold pureSourceSmoothCutoffField pureSourceRegressionCorrection pureRegressionCorrection
  rw [add_sub_cancel_left]
  change |χ (r/α)*χ (g/(N*α))*(L*((N*e-Hq)*r^p-r^(p-1)*g))| ≤
    L*(B+K+1)*2^p*N*α^p
  simpa only [one_pow,one_mul] using hscalar

end SlowEquilibration.ConditionedEntrance
