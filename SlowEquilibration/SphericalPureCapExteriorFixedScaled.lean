-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapExteriorFixedGeometry
public import SlowEquilibration.SphericalPureCapTailScale
public import SlowEquilibration.SphericalPureCapNormalizerAbsorption

/-! Scaled exterior tails vanish for one pure cap geometry chosen before
every bounded critical-energy shift window. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapExteriorFixedScaled
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapSourceScalars SphericalPureCapIntegralDecomposition
open SphericalPureCapTailScale SphericalPureCapNormalizerAbsorption
open SphericalPureCapExteriorFixedGeometry PureStationarity SphericalModel
open scoped Topology
set_option autoImplicit false

private theorem scaled_piece_vanishes
    (F r δ B C : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (s : ℕ → ℝ) (N₀ : ℕ)
    (hs0 : ∀ N ≥ N₀, 0 ≤ s N)
    (hs : ∀ N ≥ N₀,
      s N ≤ (latitudeNormalization (N-1)).toReal *
        (C*Real.exp ((N:ℝ)*(F-δ)+B))) :
    Tendsto (fun N => capScale N F r*s N) atTop (𝓝 0) := by
  obtain ⟨N₁,hNorm⟩ := latitudeNormalization_mul_fixed_eventually_le_exp
    hC (show 0 < δ/2 by positivity)
  let Nstar := max N₀ (max N₁ 2)
  apply exponentially_small_tail_vanishes F r (δ/2) B (by positivity)
    s Nstar
  · intro N hN
    exact hs0 N (by dsimp [Nstar] at hN; omega)
  · intro N hN
    have hNN₀ : N₀ ≤ N := by dsimp [Nstar] at hN; omega
    have hNN₁ : N₁ ≤ N := by dsimp [Nstar] at hN; omega
    have hN2 : 2 ≤ N := by dsimp [Nstar] at hN; omega
    have hNnorm := hNorm N hNN₁ hN2
    calc
      s N ≤ (latitudeNormalization (N-1)).toReal *
          (C*Real.exp ((N:ℝ)*(F-δ)+B)) := hs N hNN₀
      _ = (C*(latitudeNormalization (N-1)).toReal)*
          Real.exp ((N:ℝ)*(F-δ)+B) := by ring
      _ ≤ Real.exp ((N:ℝ)*(δ/2))*
          Real.exp ((N:ℝ)*(F-δ)+B) :=
            mul_le_mul_of_nonneg_right hNnorm (Real.exp_pos _).le
      _ = Real.exp ((N:ℝ)*(F-δ/2)+B) := by
        rw [←Real.exp_add]
        congr 1
        ring

private theorem profile_piece_nonneg
    (p N : ℕ) (β u l r : ℝ) (φ : ℝ → ℝ)
    (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
    0 ≤ (latitudeNormalization (N-1)).toReal *
      (∫ t in l..r, sourcePureLatitudeJacobian t *
        Real.exp ((N:ℝ)*φ t+β*u*t^p)) := by
  apply mul_nonneg ENNReal.toReal_nonneg
  apply intervalIntegral.integral_nonneg hlr
  intro t ht
  have ht' : t ∈ Icc l r := by simpa only [uIcc_of_le hlr] using ht
  have harg : 0 < 1-t^2 := by nlinarith [hl,hr,ht'.1,ht'.2]
  exact mul_nonneg (by
    unfold sourcePureLatitudeJacobian
    exact (Real.rpow_pos_of_pos harg _).le) (Real.exp_pos _).le

private theorem pole_piece_nonneg
    (p N : ℕ) (ε β H : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 ≤ (latitudeNormalization (N-1)).toReal *
      (∫ t in 1-ε..1, rawDensity p N β H t) := by
  apply mul_nonneg ENNReal.toReal_nonneg
  apply intervalIntegral.integral_nonneg (by linarith : 1-ε ≤ 1)
  intro t ht
  have ht' : t ∈ Icc (1-ε) 1 := by
    simpa only [uIcc_of_le (show 1-ε ≤ 1 by linarith)] using ht
  have ht0 : 0 ≤ t := by linarith [hε1,ht'.1]
  have hbase : 0 ≤ 1-t^2 := by nlinarith [ht0,ht'.2]
  unfold rawDensity
  exact mul_nonneg (Real.rpow_nonneg hbase _) (Real.exp_pos _).le

/-- One geometry works for every fixed `L`: both compact exterior profile
pieces and the original raw pole piece vanish at the source annealed scale. -/
theorem sourcePure_cap_exterior_fixed_scaled_vanishes
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀upper : Real.sqrt Q+b₀ < 1) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let E := markE μ β x Q
    let Λ := sourcePureLatitudeExponent p 1 Q β E
    let F := CSParisiMeasure.variationalValue μ β
    ∃ a b ε : ℝ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ b ≤ b₀ ∧
      q+b < 1-ε ∧ 0 < ε ∧ ε < 1 ∧
      pureResidualCoefficient p β a < 1/2 ∧
      pureIntensityConstant p (by omega) < β*a^p ∧ Λ q = F ∧
      ∀ L : ℝ, 0 ≤ L →
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
                (∫ t in 1-ε..1, rawDensity p N β (H N) t)))
            atTop (𝓝 0)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let Λ := sourcePureLatitudeExponent p 1 Q β (markE μ β x Q)
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨a,b,ε,δ,haHalf,hab,hb,hbb₀,hqε,hε0,hε1,hδ,hCa,hDepth,
    hcontact,hbounds⟩ := sourcePure_cap_exterior_fixed_geometry p hp h hb₀ hb₀upper
  refine ⟨a,b,ε,haHalf,hab,hb,hbb₀,hqε,hε0,hε1,hCa,hDepth,
    hcontact,?_⟩
  intro L hL
  obtain ⟨M₁,M₂,N₀,hM₁,hM₂,hLeft,hRight,hPole⟩ := hbounds L hL
  have hC₁ : 0 ≤ (q-b-a)*M₁ := mul_nonneg (by linarith [hab]) hM₁
  have hC₂ : 0 ≤ (1-ε-(q+b))*M₂ := mul_nonneg (by linarith [hqε]) hM₂
  constructor
  · intro u hu
    obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hu
    apply scaled_piece_vanishes F (1/(2*x)) δ (β*L) ((q-b-a)*M₁)
      hδ hC₁ _ (max N₀ (max N₁ 4))
    · intro N hN
      apply profile_piece_nonneg p N β (u N) a (q-b) Λ
      · exact (by positivity : 0 < 1/Real.sqrt 2).trans haHalf
      · linarith
      · exact hab.le
    · intro N hN
      have hraw := hLeft N (u N) (hN₁ N (by omega))
      exact mul_le_mul_of_nonneg_left hraw ENNReal.toReal_nonneg
  constructor
  · intro u hu
    obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hu
    apply scaled_piece_vanishes F (1/(2*x)) δ (β*L)
      ((1-ε-(q+b))*M₂) hδ hC₂ _ (max N₀ (max N₁ 4))
    · intro N hN
      apply profile_piece_nonneg p N β (u N) (q+b) (1-ε) Λ
      · have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
        linarith
      · linarith
      · exact hqε.le
    · intro N hN
      have hraw := hRight N (u N) (hN₁ N (by omega))
      exact mul_le_mul_of_nonneg_left hraw ENNReal.toReal_nonneg
  · intro H hH
    obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hH
    apply scaled_piece_vanishes F (1/(2*x)) 1 0 1
      (by norm_num) (by norm_num) _ (max N₀ (max N₁ 4))
    · intro N hN
      exact pole_piece_nonneg p N ε β (H N) hε0 hε1
    · intro N hN
      have hraw := hPole N (by omega) (by omega) (H N)
        (hN₁ N (by omega)).1 (hN₁ N (by omega)).2
      simpa only [one_mul,sub_zero,add_zero,rawDensity] using
        mul_le_mul_of_nonneg_left hraw ENNReal.toReal_nonneg

end
end SlowEquilibration.SphericalPureCapExteriorFixedScaled
