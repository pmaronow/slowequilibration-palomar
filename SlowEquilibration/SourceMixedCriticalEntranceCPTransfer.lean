-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceMixedCriticalEntranceUniformHolderTransfer
public import SlowEquilibration.SourceCriticalEntranceRateNumeric

/-! The source critical-point transfer rate, for literal original marked
critical-point sums. The ordinary posterior entrance bound and centered
expected count enter with exactly the quantifier order of the manuscript. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedCriticalEntranceCPTransfer
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open ConditionedDeterminantMoments
open SourceMixedCriticalEntranceUniformHolderTransfer
open SourceCriticalEntranceRateNumeric
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem holder_rate_factor_identity (x A C B d r : ℝ)
    (hx : 0 < x) (hC : 0 ≤ C) :
    A^(1/r)*(C*x^(-((d-2)/2)))^(1-1/r)*B =
      (A^(1/r)*C^(1-1/r)*B)*
        x^((-((d-2)/2))*(1-1/r)) := by
  rw [Real.mul_rpow hC (Real.rpow_nonneg hx.le _)]
  rw [Real.rpow_mul hx.le]
  ring

theorem actual_mixed_critical_entrance_cp_transfer
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {g Z r c C B : ℝ} (hg : 0 < g) (hr : 1 < r)
    (hc : 0 < c) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (K : (n : ℕ) → Set (EuclideanSpace ℝ (Fin 2)))
    (hK : ∀ n, MeasurableSet (K n))
    (psi : (n : ℕ) → Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ)
    (hpsi : ∀ n, Measurable fun z : Disorder (n+2) μ.maxDegree ×
      Vector (n+2) => psi n z.1 z.2)
    (hpsi01 : ∀ n J u, 0 ≤ psi n J u ∧ psi n J u ≤ 1)
    (hgap : ∀ n, ∀ z ∈ K n,
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 ∧ z 1 ≤ Z)
    (hordinary : ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
      (z : EuclideanSpace ℝ (Fin 2)), z ∈ K n →
        (∫ J, psi n J u ∂mixedLaw μ Q u hu z) ≤
          C*(((n+2 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
            ((n+2 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
            Real.exp (-c*((n+2 : ℕ) : ℝ)))
    (hcount : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) (K n)
          (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal B) :
    ∃ Cdet : ℝ, 0 < Cdet ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q) (K n)
          (fun J u => ENNReal.ofReal (psi n J u)) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal ((Cdet^(1/r)*(2*C+1)^(1-1/r)*B)*
          (((n+2 : ℕ) : ℝ)^
            ((-(((μ.minDegree : ℝ)-2)/2))*(1-1/r)))) := by
  obtain ⟨Cdet,hCdet,hTransfer⟩ :=
    actual_mixed_critical_entrance_holder_transfer_uniform
      μ hQ hnp (Z := Z) (r := r) hg hr
  refine ⟨Cdet,hCdet,?_⟩
  have hdReal : (4 : ℝ) ≤ (μ.minDegree : ℝ) := by exact_mod_cast hd
  have hRate := entrance_source_rate_le_single_power_eventually
    (d := (μ.minDegree : ℝ)) hdReal hc hC
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hRate
  filter_upwards [hordinary,hcount,eventually_ge_atTop N] with n hn hcn hNn
  let x : ℝ := ((n+2 : ℕ) : ℝ)
  let α : ℝ := ((μ.minDegree : ℝ)-2)/2
  let s : ℝ := 1-1/r
  let q : ℝ := (2*C+1)*x^(-α)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hC1 : 0 ≤ 2*C+1 := by linarith
  have hq : 0 ≤ q := mul_nonneg hC1 (Real.rpow_nonneg hx.le _)
  have hRN : C*(x^(1-(μ.minDegree : ℝ)/2)+
      x^(3-(μ.minDegree : ℝ)))+Real.exp (-c*x) ≤ q := by
    have heq : -((μ.minDegree : ℝ)-2)/2 =
        -(((μ.minDegree : ℝ)-2)/2) := by ring
    simpa only [x,α,q,heq,show n+1+1=n+2 by omega] using
      hN (n+1) (by omega)
  have hordinary' (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
      (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ K n) :
      (∫ J, psi n J u ∂mixedLaw μ Q u hu z) ≤ q :=
    (hn u hu z hz).trans hRN
  have hpoint := hTransfer n (K n) (hK n) (psi n) (hpsi n)
    (hpsi01 n) q hq (hgap n) hordinary'
  have hfactor : 0 ≤ Cdet^(1/r)*q^s :=
    mul_nonneg (Real.rpow_nonneg hCdet.le _) (Real.rpow_nonneg hq _)
  have hbound := hpoint.trans
    (mul_le_mul_right hcn (ENNReal.ofReal (Cdet^(1/r)*q^s)))
  have hmul : ENNReal.ofReal (Cdet^(1/r)*q^s)*ENNReal.ofReal B =
      ENNReal.ofReal ((Cdet^(1/r)*q^s)*B) :=
    (ENNReal.ofReal_mul hfactor).symm
  rw [hmul] at hbound
  have hidentity : (Cdet^(1/r)*q^s)*B =
      (Cdet^(1/r)*(2*C+1)^s*B)*x^(-α*s) := by
    simpa only [q,s,α] using
      holder_rate_factor_identity x Cdet (2*C+1) B
        (μ.minDegree : ℝ) r hx hC1
  rw [hidentity] at hbound
  simpa only [x,α,s] using hbound

end SlowEquilibration.SourceMixedCriticalEntranceCPTransfer
