-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapNormalizerAbsorption

@[expose] public section

/-! The source pure §9.19 exterior integral tails with the literal spherical
coarea normalization, under one cap and one contact band. -/

namespace SlowEquilibration.SphericalPureCapExteriorNormalized
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity MeasureTheory
open SphericalTAPCriticalPureLatitudeProfile
open SphericalPureLaplaceRegularity
open SphericalPureCapSourceScalars
open SphericalPureCapExteriorTailPackage
open SphericalPureCapNormalizerAbsorption
open PureStationarity SphericalModel
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- After multiplying by the actual coarea factor, both compact exterior
pieces and the pole remain exponentially below the pure contact free energy.
The same cap latitude and contact window work for all fixed energy shifts
`u ≤ L`, and for all sufficiently large dimensions. -/
theorem sourcePure_cap_exterior_normalized_tails
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
      (∀ N ≥ N₀, 4 ≤ N → ∀ u : ℝ, u ≤ L →
        (latitudeNormalization (N-1)).toReal *
          (∫ t in a..(q-b), sourcePureLatitudeJacobian t *
            Real.exp ((N:ℝ)*Λ t+β*u*t^p)) ≤
              Real.exp ((N:ℝ)*(F-δ/2)+β*L)) ∧
      (∀ N ≥ N₀, 4 ≤ N → ∀ u : ℝ, u ≤ L →
        (latitudeNormalization (N-1)).toReal *
          (∫ t in (q+b)..(1-ε), sourcePureLatitudeJacobian t *
            Real.exp ((N:ℝ)*Λ t+β*u*t^p)) ≤
              Real.exp ((N:ℝ)*(F-δ/2)+β*L)) ∧
      (∀ N ≥ N₀, 4 ≤ N → ∀ H : ℝ,
        0 ≤ H → H ≤ (N:ℝ)*pureEnergyConstant p (by omega)+L →
        (latitudeNormalization (N-1)).toReal *
          (∫ t in (1-ε)..1,
            (1-t^2)^(((N:ℝ)-3)/2) *
              Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
            Real.exp ((N:ℝ)*(F-1/2))) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  let E := markE μ β x Q
  let Λ := sourcePureLatitudeExponent p 1 Q β E
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨a,b,ε,δ,M₁,M₂,N₀,haHalf,hal,hb,hbb₀,hεr,hε0,hε1,hδ,
    hM₁,hM₂,hCa,hDepth,hcontact,hLeft,hRight,hPole⟩ :=
      sourcePure_cap_exterior_tail_package p hp h hb₀ hb₀upper hL
  let C₁ := (q-b-a)*M₁
  let C₂ := (1-ε-(q+b))*M₂
  have hC₁ : 0 ≤ C₁ := mul_nonneg (by dsimp [q]; linarith [hal]) hM₁
  have hC₂ : 0 ≤ C₂ := mul_nonneg (by dsimp [q]; linarith [hεr]) hM₂
  obtain ⟨N₁,hNorm₁⟩ := latitudeNormalization_mul_fixed_eventually_le_exp
    hC₁ (show 0 < δ/2 by positivity)
  obtain ⟨N₂,hNorm₂⟩ := latitudeNormalization_mul_fixed_eventually_le_exp
    hC₂ (show 0 < δ/2 by positivity)
  obtain ⟨N₃,hNorm₃⟩ := latitudeNormalization_mul_fixed_eventually_le_exp
    (show 0 ≤ (1:ℝ) by norm_num) (show 0 < (1/2:ℝ) by norm_num)
  let Nstar := max N₀ (max N₁ (max N₂ N₃))
  refine ⟨a,b,ε,δ,Nstar,haHalf,hal,hb,hbb₀,hεr,hε0,hε1,hδ,hCa,
    hDepth,hcontact,?_,?_,?_⟩
  · intro N hNNstar hN u hu
    have hNN₁ : N₁ ≤ N := by dsimp [Nstar] at hNNstar; omega
    have hNorm := hNorm₁ N hNN₁ (by omega : 2 ≤ N)
    have hInt := hLeft N u hu
    have hNorm0 : 0 ≤ (latitudeNormalization (N-1)).toReal := ENNReal.toReal_nonneg
    calc
      (latitudeNormalization (N-1)).toReal *
          (∫ t in a..(q-b), sourcePureLatitudeJacobian t *
            Real.exp ((N:ℝ)*Λ t+β*u*t^p)) ≤
        (latitudeNormalization (N-1)).toReal *
          (C₁*Real.exp ((N:ℝ)*(F-δ)+β*L)) := by
            exact mul_le_mul_of_nonneg_left hInt hNorm0
      _ = (C₁*(latitudeNormalization (N-1)).toReal)*
            Real.exp ((N:ℝ)*(F-δ)+β*L) := by ring
      _ ≤ Real.exp ((N:ℝ)*(δ/2))*Real.exp ((N:ℝ)*(F-δ)+β*L) :=
            mul_le_mul_of_nonneg_right hNorm (Real.exp_pos _).le
      _ = Real.exp ((N:ℝ)*(F-δ/2)+β*L) := by
            rw [←Real.exp_add]
            congr 1
            ring
  · intro N hNNstar hN u hu
    have hNN₂ : N₂ ≤ N := by dsimp [Nstar] at hNNstar; omega
    have hNorm := hNorm₂ N hNN₂ (by omega : 2 ≤ N)
    have hInt := hRight N u hu
    have hNorm0 : 0 ≤ (latitudeNormalization (N-1)).toReal := ENNReal.toReal_nonneg
    calc
      (latitudeNormalization (N-1)).toReal *
          (∫ t in (q+b)..(1-ε), sourcePureLatitudeJacobian t *
            Real.exp ((N:ℝ)*Λ t+β*u*t^p)) ≤
        (latitudeNormalization (N-1)).toReal *
          (C₂*Real.exp ((N:ℝ)*(F-δ)+β*L)) := by
            exact mul_le_mul_of_nonneg_left hInt hNorm0
      _ = (C₂*(latitudeNormalization (N-1)).toReal)*
            Real.exp ((N:ℝ)*(F-δ)+β*L) := by ring
      _ ≤ Real.exp ((N:ℝ)*(δ/2))*Real.exp ((N:ℝ)*(F-δ)+β*L) :=
            mul_le_mul_of_nonneg_right hNorm (Real.exp_pos _).le
      _ = Real.exp ((N:ℝ)*(F-δ/2)+β*L) := by
            rw [←Real.exp_add]
            congr 1
            ring
  · intro N hNNstar hN H hH0 hH
    have hNN₀ : N₀ ≤ N := by dsimp [Nstar] at hNNstar; omega
    have hNN₃ : N₃ ≤ N := by dsimp [Nstar] at hNNstar; omega
    have hNorm := hNorm₃ N hNN₃ (by omega : 2 ≤ N)
    have hInt := hPole N hNN₀ hN H hH0 hH
    have hNorm0 : 0 ≤ (latitudeNormalization (N-1)).toReal := ENNReal.toReal_nonneg
    calc
      (latitudeNormalization (N-1)).toReal *
          (∫ t in (1-ε)..1,
            (1-t^2)^(((N:ℝ)-3)/2) *
              Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
        (latitudeNormalization (N-1)).toReal * Real.exp ((N:ℝ)*(F-1)) :=
            mul_le_mul_of_nonneg_left hInt hNorm0
      _ ≤ Real.exp ((N:ℝ)*(1/2))*Real.exp ((N:ℝ)*(F-1)) := by
            have hh : (latitudeNormalization (N-1)).toReal ≤ Real.exp ((N:ℝ)*(1/2)) := by
              simpa only [one_mul] using hNorm
            exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = Real.exp ((N:ℝ)*(F-1/2)) := by
            rw [←Real.exp_add]
            congr 1
            ring

end
end SlowEquilibration.SphericalPureCapExteriorNormalized
