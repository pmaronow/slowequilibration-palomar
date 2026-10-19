-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceMixedCenteredCriticalEntranceTransfer
public import SlowEquilibration.ConditionedEntranceSourceTruePosteriorLaw

/-! The centered critical-point transfer for the literal true diffusion,
using only an original-disorder source corrected-field entrance rate. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedCenteredTrueEntranceTransfer
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalForm
open SphericalSmoothParameter
open ConditionedDeterminantMoments ConditionedEntrance
open SourceMixedCenteredCriticalEntranceTransfer
open SphericalTAPCertificate
open scoped ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem originalTrueCapHitProbability_joint_measurable
    {N : ℕ} (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (a : ℝ) :
    Measurable (fun z : Disorder N μ.maxDegree × Vector N =>
      originalTrueCapHitProbability μ β T a z.2 z.1) := by
  exact (uniformCapHitProbability_measurable β
    (jointSpatialGradient (originalTrueJointHamiltonian μ))
    (jointSpatialGradient_contDiff _ (originalTrueJointHamiltonian_contDiff μ))
    T a).comp (measurable_snd.prodMk measurable_fst)

theorem source_mixed_centered_true_entrance_cp_transfer
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β x L R : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R)
    {g Z r c C M a : ℝ} (hg : 0 < g) (hr : 1 < r)
    (hc : 0 < c) (hC : 0 ≤ C) (hM : 0 < M) (_ha : 0 < a)
    (hL : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ L) (hR : R ≤ Z)
    (H : ℕ → ℝ≥0)
    (hsource : ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (_hu : ‖u‖^2=((n+2:ℕ):ℝ))
      (e k : ℝ),
      scorePairEquiv (e,k) ∈ physicalEnergyWindow (n+2)
        (Icc (d.center n-M) (d.center n+M)) (Ioo L R) →
        (∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
          (fun _ => 1) contDiff_const β (H n) (J,(u,(e,k)))
          ∂disorderLaw (n+2) μ.maxDegree) ≤
          C*(((n+2 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
            ((n+2 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
            Real.exp (-c*((n+2 : ℕ) : ℝ))) :
    ∃ (B Cdet : ℝ), 0 < B ∧ 0 < Cdet ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+2)
            (Icc (d.center n-M) (d.center n+M)) (Ioo L R))
          (fun J u => ENNReal.ofReal
            (originalTrueCapHitProbability μ β (H n) a u J)) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal ((Cdet^(1/r)*(2*C+1)^(1-1/r)*B)*
          (((n+2 : ℕ) : ℝ)^
            ((-(((μ.minDegree : ℝ)-2)/2))*(1-1/r)))) := by
  let psi (n : ℕ) (J : Disorder (n+2) μ.maxDegree)
      (u : Vector (n+2)) : ℝ :=
    originalTrueCapHitProbability μ β (H n) a u J
  have hpsi (n : ℕ) : Measurable fun z : Disorder (n+2) μ.maxDegree ×
      Vector (n+2) => psi n z.1 z.2 :=
    originalTrueCapHitProbability_joint_measurable μ β (H n) a
  have hpsi01 (n : ℕ) (J : Disorder (n+2) μ.maxDegree)
      (u : Vector (n+2)) : 0 ≤ psi n J u ∧ psi n J u ≤ 1 :=
    originalTrueCapHitProbability_mem_unit μ β (H n) a u J
  have hordinary : ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
      (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ physicalEnergyWindow (n+2)
        (Icc (d.center n-M) (d.center n+M)) (Ioo L R) →
        (∫ J, psi n J u ∂mixedLaw μ Q u hu z) ≤
          C*(((n+2 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
            ((n+2 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
            Real.exp (-c*((n+2 : ℕ) : ℝ)) := by
    filter_upwards [hsource] with n hn
    intro u hu z hz
    let e : ℝ := (scorePairEquiv.symm z).1
    let k : ℝ := (scorePairEquiv.symm z).2
    have hpair : scorePairEquiv (e,k) = z := by
      simpa only [e,k,Prod.mk.eta] using scorePairEquiv.apply_symm_apply z
    have hhalf : (2*a)/2 = a := by ring
    have hLaw := originalTrueCapHitProbability_mixedPalm_integral_eq_source_one
      (n+1) μ hQ hnp u (by simpa only [show n+1+1=n+2 by omega] using hu)
      e k (2*a) β (H n)
    have hSource := hn u hu e k (hpair ▸ hz)
    change (∫ J, psi n J u ∂mixedLaw μ Q u hu z) ≤ _
    have hLaw' : (∫ J, psi n J u ∂mixedLaw μ Q u hu z) =
        ∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
          (fun _ => 1) contDiff_const β (H n) (J,(u,(e,k)))
          ∂disorderLaw (n+2) μ.maxDegree := by
      rw [← hpair]
      simpa only [psi,hhalf,show n+1+1=n+2 by omega,
        mixedLaw,mixedConditionedLaw] using hLaw
    exact hLaw'.le.trans hSource
  exact source_mixed_centered_critical_entrance_cp_transfer_of_ordinary
    μ hd hQ hnp d hg hr hc hC hM hL hR psi hpsi hpsi01 hordinary

end SlowEquilibration.SourceMixedCenteredTrueEntranceTransfer
