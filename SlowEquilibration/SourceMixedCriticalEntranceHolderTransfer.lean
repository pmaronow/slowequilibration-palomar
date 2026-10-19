-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalTAPCriticalLightCountTransfer
public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.DeterminantHolder

/-! Determinant-weighted Kac--Rice transfer of any bounded whole-field
entrance mark, starting from its ordinary physical Gaussian posterior mean. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedCriticalEntranceHolderTransfer
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalSequentialRegression IntrinsicHessianLaw SphereHessian
open ConditionedDeterminantMoments SphericalTAPCriticalLightCountTransfer
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem actual_mixed_critical_entrance_holder_transfer
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    {g Z r q : ℝ} (hg : 0 < g) (hr : 1 < r) (hq : 0 ≤ q)
    (hgap : ∀ z ∈ K,
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 ∧ z 1 ≤ Z)
    (psi : Disorder (d+2) μ.maxDegree → Vector (d+2) → ℝ)
    (hpsi : Measurable fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
      psi z.1 z.2)
    (hpsi01 : ∀ J u, 0 ≤ psi J u ∧ psi J u ≤ 1)
    (hordinary : ∀ (u : Vector (d+2))
      (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ K →
      (∫ J, psi J u ∂mixedLaw μ Q u hu z) ≤ q) :
    ∃ Cdet : ℝ, 0 < Cdet ∧
      (∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K
        (fun J u => ENNReal.ofReal (psi J u)) J
        ∂disorderLaw (d+2) μ.maxDegree) ≤
      ENNReal.ofReal (Cdet^(1/r)*q^(1-1/r)) *
        (∫⁻ J, actualScoreWindowCount (d+1)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (d+2) μ.maxDegree) := by
  obtain ⟨Cdet,hCdet,hM⟩ :=
    mixed_conditioned_determinant_moments μ hQ hnp (Z := Z) (r := r)
      hg (by linarith)
  refine ⟨Cdet,hCdet,?_⟩
  apply actual_mixed_marked_count_le_of_uniform_palm d μ hQ hnp K hK
    (fun J u => ENNReal.ofReal (psi J u))
    (ENNReal.measurable_ofReal.comp hpsi) (ENNReal.ofReal_ne_top) ?_
  intro u hu z hz
  let ν := mixedLaw μ Q u hu z
  let D := intrinsicDet μ Q u
  let φ : Disorder (d+2) μ.maxDegree → ℝ := fun J => psi J u
  have hP : IsProbabilityMeasure ν := by
    dsimp [ν,mixedLaw]
    infer_instance
  have hφm : Measurable φ := by
    exact hpsi.comp (measurable_id.prodMk measurable_const)
  have hφ01 : ∀ J, 0 ≤ φ J ∧ φ J ≤ 1 := fun J => hpsi01 J u
  have hφnorm : ∀ᵐ J ∂ν, ‖φ J‖ ≤ (1 : ℝ) :=
    .of_forall fun J => by rw [Real.norm_of_nonneg (hφ01 J).1]; exact (hφ01 J).2
  have hp := hM d u hu z (hgap z hz).1 (hgap z hz).2
  have hholder := determinant_weighted_holder ν D φ hp.1
    (.of_forall fun J => abs_nonneg _)
    hp.2.2.1 hφm.aestronglyMeasurable (.of_forall hφ01)
    hr hp.2.2.2.1 hp.2.2.2.2 (hordinary u hu z hz)
  have hreal : (∫ J, D J * φ J ∂ν) ≤
      Cdet^(1/r)*q^(1-1/r)*(∫ J, D J ∂ν) :=
    (div_le_iff₀ hp.2.2.1).mp hholder
  have hprod : Integrable (fun J => D J*φ J) ν :=
    hp.1.mul_bdd hφm.aestronglyMeasurable hφnorm
  have hprodENN :
      (∫⁻ J, ENNReal.ofReal (D J)*ENNReal.ofReal (φ J) ∂ν) =
        ENNReal.ofReal (∫ J, D J*φ J ∂ν) := by
    calc
      _ = ∫⁻ J, ENNReal.ofReal (D J*φ J) ∂ν := by
        apply lintegral_congr
        intro J
        exact (ENNReal.ofReal_mul (abs_nonneg _)).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hprod
        (.of_forall fun J => mul_nonneg (abs_nonneg _) (hφ01 J).1)).symm
  have hmeanENN :
      ENNReal.ofReal (∫ J, D J ∂ν) = ∫⁻ J, ENNReal.ofReal (D J) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hp.1 (.of_forall fun J => abs_nonneg _)
  have hconst : 0 ≤ Cdet^(1/r)*q^(1-1/r) :=
    mul_nonneg (Real.rpow_nonneg hCdet.le _) (Real.rpow_nonneg hq _)
  change (∫⁻ J, ENNReal.ofReal (D J)*ENNReal.ofReal (φ J) ∂ν) ≤
    ENNReal.ofReal (Cdet^(1/r)*q^(1-1/r)) *
      (∫⁻ J, ENNReal.ofReal (D J) ∂ν)
  calc
    _ = ENNReal.ofReal (∫ J, D J*φ J ∂ν) := hprodENN
    _ ≤ ENNReal.ofReal
      (Cdet^(1/r)*q^(1-1/r)*(∫ J, D J ∂ν)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Cdet^(1/r)*q^(1-1/r)) *
        ENNReal.ofReal (∫ J, D J ∂ν) := ENNReal.ofReal_mul hconst
    _ = _ := by rw [hmeanENN]

end SlowEquilibration.SourceMixedCriticalEntranceHolderTransfer
