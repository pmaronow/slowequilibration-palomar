-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapIntegralDecomposition
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! The exponential pure cap exterior bounds vanish at the manuscript's
polynomially corrected annealed scale. -/

namespace SlowEquilibration.SphericalPureCapTailScale
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapExteriorNormalized SphericalPureCapSourceScalars
open SphericalPureCapIntegralDecomposition
open SphericalModel PureStationarity
open scoped Topology
set_option autoImplicit false

/-- The normalization that removes the pure contact free energy and its
polynomial correction. -/
def capScale (N : ℕ) (F r : ℝ) : ℝ :=
  (N:ℝ)^r * Real.exp (-(N:ℝ)*F)

theorem capScale_nonneg (N : ℕ) (F r : ℝ) :
    0 ≤ capScale N F r := by
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le

/-- Any exponentially smaller nonnegative tail disappears at the source
scale, regardless of the real polynomial exponent. -/
theorem exponentially_small_tail_vanishes
    (F r δ B : ℝ) (hδ : 0 < δ) (s : ℕ → ℝ) (N₀ : ℕ)
    (hs0 : ∀ N ≥ N₀, 0 ≤ s N)
    (hs : ∀ N ≥ N₀,
      s N ≤ Real.exp ((N:ℝ)*(F-δ)+B)) :
    Tendsto (fun N => capScale N F r * s N) atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun N : ℕ => (N:ℝ)^r * Real.exp (-δ*(N:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero r δ hδ).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun N : ℕ =>
      capScale N F r * Real.exp ((N:ℝ)*(F-δ)+B)) atTop (𝓝 0) := by
    have heq : (fun N : ℕ =>
        capScale N F r * Real.exp ((N:ℝ)*(F-δ)+B)) =
        (fun N : ℕ => Real.exp B *
          ((N:ℝ)^r * Real.exp (-δ*(N:ℝ)))) := by
      funext N
      dsimp [capScale]
      calc
        (N:ℝ)^r * Real.exp (-(N:ℝ)*F) *
            Real.exp ((N:ℝ)*(F-δ)+B) =
          (N:ℝ)^r * Real.exp (-(N:ℝ)*F+((N:ℝ)*(F-δ)+B)) := by
            rw [mul_assoc, ←Real.exp_add]
        _ = Real.exp B * ((N:ℝ)^r * Real.exp (-δ*(N:ℝ))) := by
          rw [show -(N:ℝ)*F+((N:ℝ)*(F-δ)+B) = -δ*(N:ℝ)+B by ring,
            Real.exp_add]
          ring
    rw [heq]
    simpa only [mul_zero] using hbase.const_mul (Real.exp B)
  apply squeeze_zero'
    (by
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact mul_nonneg (capScale_nonneg N F r) (hs0 N hN))
    (by
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact mul_le_mul_of_nonneg_left (hs N hN) (capScale_nonneg N F r))
    hupper

private theorem profile_piece_nonneg
    (p N : ℕ) (β u l r : ℝ) (φ : ℝ → ℝ)
    (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
    0 ≤ (latitudeNormalization (N-1)).toReal *
      (∫ t in l..r,
        sourcePureLatitudeJacobian t *
          Real.exp ((N:ℝ)*φ t+β*u*t^p)) := by
  apply mul_nonneg ENNReal.toReal_nonneg
  apply intervalIntegral.integral_nonneg hlr
  intro t ht
  have ht' : t ∈ Icc l r := by simpa only [uIcc_of_le hlr] using ht
  have harg : 0 < 1-t^2 := by nlinarith [hl,hr,ht'.1,ht'.2]
  exact mul_nonneg (by
    unfold sourcePureLatitudeJacobian
    exact (Real.rpow_pos_of_pos harg _).le) (Real.exp_pos _).le

/-- The source §9 compact exterior bounds vanish at the exact annealed
scale, with one cap and contact band simultaneously for both pieces. -/
theorem sourcePure_compact_exterior_scaled_vanishes
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {b₀ L : ℝ} (hb₀ : 0 < b₀)
    (hb₀upper : Real.sqrt Q+b₀ < 1) (hL : 0 ≤ L) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let E := markE μ β x Q
    let Λ := sourcePureLatitudeExponent p 1 Q β E
    let F := CSParisiMeasure.variationalValue μ β
    ∃ a b ε δ : ℝ, ∃ N₀ : ℕ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ b ≤ b₀ ∧
      q+b < 1-ε ∧ 0 < ε ∧ ε < 1 ∧ 0 < δ ∧
      pureResidualCoefficient p β a < 1/2 ∧
      pureIntensityConstant p (by omega) < β*a^p ∧
      Λ q = F ∧
      (∀ u : ℕ → ℝ, (∀ᶠ N in atTop, u N ≤ L) →
        Tendsto (fun N : ℕ =>
          capScale N F (1/(2*x)) *
            ((latitudeNormalization (N-1)).toReal *
              (∫ t in a..q-b, sourcePureLatitudeJacobian t *
                Real.exp ((N:ℝ)*Λ t+β*(u N)*t^p)))) atTop (𝓝 0)) ∧
      (∀ u : ℕ → ℝ, (∀ᶠ N in atTop, u N ≤ L) →
        Tendsto (fun N : ℕ =>
          capScale N F (1/(2*x)) *
            ((latitudeNormalization (N-1)).toReal *
              (∫ t in q+b..1-ε, sourcePureLatitudeJacobian t *
                Real.exp ((N:ℝ)*Λ t+β*(u N)*t^p)))) atTop (𝓝 0)) ∧
      (∀ H : ℕ → ℝ,
        (∀ᶠ N in atTop,
          0 ≤ H N ∧ H N ≤ (N:ℝ)*pureEnergyConstant p (by omega)+L) →
        Tendsto (fun N : ℕ =>
          capScale N F (1/(2*x)) *
            ((latitudeNormalization (N-1)).toReal *
              (∫ t in 1-ε..1, rawDensity p N β (H N) t))) atTop (𝓝 0)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let E := markE μ β x Q
  let Λ := sourcePureLatitudeExponent p 1 Q β E
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨a,b,ε,δ,N₀,haHalf,hal,hb,hbb₀,hεr,hε0,hε1,hδ,hCa,
    hDepth,hcontact,hLeft,hRight,hPole⟩ :=
      sourcePure_cap_exterior_normalized_tails p hp h hb₀ hb₀upper hL
  refine ⟨a,b,ε,δ,N₀,haHalf,hal,hb,hbb₀,hεr,hε0,hε1,hδ,
    hCa,hDepth,hcontact,?_,?_,?_⟩
  · intro u hu
    obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hu
    apply exponentially_small_tail_vanishes F (1/(2*x)) (δ/2)
      (β*L) (by positivity)
      (fun N => (latitudeNormalization (N-1)).toReal *
        (∫ t in a..q-b, sourcePureLatitudeJacobian t *
          Real.exp ((N:ℝ)*Λ t+β*(u N)*t^p))) (max N₀ (max N₁ 4))
    · intro N hN
      apply profile_piece_nonneg p N β (u N) a (q-b) Λ
      · have : 0 < 1/Real.sqrt 2 := by positivity
        linarith
      · linarith
      · exact hal.le
    · intro N hN
      exact hLeft N (by omega) (by omega) (u N) (hN₁ N (by omega))
  · intro u hu
    obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hu
    apply exponentially_small_tail_vanishes F (1/(2*x)) (δ/2)
      (β*L) (by positivity)
      (fun N => (latitudeNormalization (N-1)).toReal *
        (∫ t in q+b..1-ε, sourcePureLatitudeJacobian t *
          Real.exp ((N:ℝ)*Λ t+β*(u N)*t^p))) (max N₀ (max N₁ 4))
    · intro N hN
      apply profile_piece_nonneg p N β (u N) (q+b) (1-ε) Λ
      · have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
        linarith
      · linarith
      · exact hεr.le
    · intro N hN
      exact hRight N (by omega) (by omega) (u N) (hN₁ N (by omega))
  · intro H hH
    obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hH
    apply exponentially_small_tail_vanishes F (1/(2*x)) (1/2)
      0 (by norm_num)
      (fun N => (latitudeNormalization (N-1)).toReal *
        (∫ t in 1-ε..1, rawDensity p N β (H N) t))
      (max N₀ (max N₁ 4))
    · intro N hN
      apply mul_nonneg ENNReal.toReal_nonneg
      apply intervalIntegral.integral_nonneg (by linarith : 1-ε ≤ 1)
      intro t ht
      have ht' : t ∈ Icc (1-ε) 1 := by
        simpa only [uIcc_of_le (show 1-ε ≤ 1 by linarith)] using ht
      have hbase : 0 ≤ 1-t^2 := by
        have ht0 : 0 ≤ t := by linarith [hε1,ht'.1]
        nlinarith [ht0,ht'.2]
      unfold rawDensity
      exact mul_nonneg (Real.rpow_nonneg hbase _) (Real.exp_pos _).le
    · intro N hN
      have hHN : 0 ≤ H N ∧ H N ≤ (N:ℝ)*pureEnergyConstant p (by omega)+L :=
        hN₁ N (by omega)
      simpa only [rawDensity, add_zero] using
        hPole N (by omega) (by omega) (H N) hHN.1 hHN.2

end
end SlowEquilibration.SphericalPureCapTailScale
