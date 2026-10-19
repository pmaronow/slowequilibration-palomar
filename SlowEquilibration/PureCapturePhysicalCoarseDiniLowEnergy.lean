-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalLowEnergyMeasurability

/-! A single genuine replicated-mean energy estimate controls the finite
query-plus-block low-energy error by a union bound. The source energy input
is stated for ordinary Gibbs replicas, before any successful query is selected. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalCoarseDiniLowEnergy
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalGaussianJet PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer PureCapturePhysicalFiniteMeasurability
open PureCapturePhysicalLowEnergyMeasurability PureCapturePhysicalCoarseLimit
open scoped Topology BigOperators
set_option autoImplicit false

def replicaMeanLowEnergy {N k : ℕ} (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (Q η e τ : ℝ) : Set (Fin k → Vector N) :=
  {σ | (∀ i j : Fin k, i ≠ j → |overlap (σ i) (σ j)-Q| < η) ∧
    field (mixtureCoefficients μ) J (physicalTrainingCenter σ) ≤ (N:ℝ)*(e-τ)}

set_option maxHeartbeats 1400000 in
theorem joint_replicaMeanLowEnergy_measurable {n k : ℕ}
    (μ : FiniteMixture) (Q η e τ : ℝ) :
    MeasurableSet {p : Disorder (n+2) μ.maxDegree × (Fin k → Vector (n+2)) |
      p.2 ∈ replicaMeanLowEnergy μ p.1 Q η e τ} := by
  have hpair : MeasurableSet {p : Disorder (n+2) μ.maxDegree × (Fin k → Vector (n+2)) |
      ∀ i j : Fin k, i ≠ j → |overlap (p.2 i) (p.2 j)-Q| < η} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · have hmap : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
          (Fin k → Vector (n+2)) => (p.2 i, p.2 j)) :=
        ((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_snd)
      have hm : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
          (Fin k → Vector (n+2)) => overlap (p.2 i) (p.2 j)) :=
        overlap_joint_continuous.measurable.comp hmap
      simpa only [hij,ne_eq,not_false_eq_true,iInter_true,Function.comp_def] using
        measurableSet_lt (continuous_abs.measurable.comp (hm.sub_const Q)) measurable_const
  have hmap : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
      (Fin k → Vector (n+2)) => (p.1, physicalTrainingCenter p.2)) :=
    measurable_fst.prodMk (physicalTrainingCenter_measurable.comp measurable_snd)
  have hfield : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
      (Fin k → Vector (n+2)) =>
      field (mixtureCoefficients μ) p.1 (physicalTrainingCenter p.2)) :=
    (field_jointContinuous (mixtureCoefficients μ)).measurable.comp hmap
  exact hpair.inter (measurableSet_le hfield measurable_const)

def expectedReplicaMeanLowEnergy {k : ℕ} (n : ℕ) (μ : FiniteMixture)
    (β Q η e τ : ℝ) : ℝ :=
  ∫ J, (Measure.pi (fun _ : Fin k =>
    gibbsLaw (n+2) β (field (mixtureCoefficients μ) J))).real
      (replicaMeanLowEnergy μ J Q η e τ) ∂disorderLaw (n+2) μ.maxDegree

theorem replicaMeanLowEnergy_probability_integrable {n k : ℕ}
    (μ : FiniteMixture) (β Q η e τ : ℝ) :
    Integrable (fun J : Disorder (n+2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real (replicaMeanLowEnergy μ J Q η e τ))
      (disorderLaw (n+2) μ.maxDegree) := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  have h := (Kernel.measurable_kernel_prodMk_left
    (κ := GaussianReplicaKernel.iid G k)
      (joint_replicaMeanLowEnergy_measurable (k := k) μ Q η e τ)).ennreal_toReal
  have hm : Measurable (fun J : Disorder (n+2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real (replicaMeanLowEnergy μ J Q η e τ)) := by
    convert h using 1
    funext J
    simp only [GaussianReplicaKernel.iid_apply, G, allDimensionGibbsKernel_apply]
    rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact .of_forall fun J => by
    let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
      gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

set_option maxHeartbeats 1400000 in
theorem finiteLowEnergy_le_replicaMeanLowEnergy {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ η e τ : ℝ) (hθη : θ ≤ η)
    (J : Disorder (n+2) μ.maxDegree) :
    (physicalEnsembleLaw (k := k) (T := T) μ β J).real
      (someSuccessfulBlockLowEnergy μ J Q θ e τ) ≤
      (T:ℝ)*(Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real (replicaMeanLowEnergy μ J Q η e τ) := by
  let π := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
  let ρ := Measure.pi (fun _ : Fin k => π)
  let ν := physicalEnsembleLaw (k := k) (T := T) μ β J
  let E := replicaMeanLowEnergy (k := k) μ J Q η e τ
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  have hE : MeasurableSet E :=
    (joint_replicaMeanLowEnergy_measurable (k := k) μ Q η e τ).preimage
      (measurable_const.prodMk measurable_id)
  have hsub : someSuccessfulBlockLowEnergy (T := T) μ J Q θ e τ ⊆
      ⋃ b : Fin T, {p : PhysicalEnsemble (n+2) k T | p.2 b ∈ E} := by
    rintro p ⟨b,hgood,hlow⟩
    refine Set.mem_iUnion.mpr ⟨b,?_⟩
    exact ⟨fun i j hij => (hgood.1 i j hij).trans_le hθη,hlow.le⟩
  have hmarg (b : Fin T) :
      ν.real {p : PhysicalEnsemble (n+2) k T | p.2 b ∈ E} = ρ.real E := by
    have hMP : MeasurePreserving (fun p : PhysicalEnsemble (n+2) k T => p.2 b) ν ρ :=
      (measurePreserving_eval (μ := fun _ : Fin T => ρ) b).comp measurePreserving_snd
    exact hMP.measureReal_preimage hE.nullMeasurableSet
  calc
    _ ≤ ν.real (⋃ b : Fin T, {p : PhysicalEnsemble (n+2) k T | p.2 b ∈ E}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ b : Fin T, ν.real {p : PhysicalEnsemble (n+2) k T | p.2 b ∈ E} :=
      measureReal_iUnion_fintype_le _
    _ = _ := by
      simp only [hmarg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rfl

theorem expectedFiniteLowEnergy_tendsto_zero_of_replica_mean {k : ℕ}
    (μ : FiniteMixture) (β Q θ η e τ : ℝ) (hθη : θ ≤ η)
    (hMean : Tendsto (fun n => expectedReplicaMeanLowEnergy (k := k) n μ β Q η e τ)
      atTop (𝓝 (0:ℝ))) (T : ℕ) :
    Tendsto (fun n => expectedFiniteLowEnergy (n := n) (k := k) (T := T)
      μ β Q θ e τ) atTop (𝓝 (0:ℝ)) := by
  have hbound (n : ℕ) : expectedFiniteLowEnergy (n := n) (k := k) (T := T)
      μ β Q θ e τ ≤ (T:ℝ)*expectedReplicaMeanLowEnergy (k := k) n μ β Q η e τ := by
    have hh := integral_mono
      (finiteLowEnergyProbability_integrable (n := n) (k := k) (T := T) μ β Q θ e τ)
      ((replicaMeanLowEnergy_probability_integrable (n := n) (k := k)
        μ β Q η e τ).const_mul (T:ℝ))
      (finiteLowEnergy_le_replicaMeanLowEnergy (n := n) (k := k) (T := T)
        μ β Q θ η e τ hθη)
    simpa only [expectedFiniteLowEnergy,expectedReplicaMeanLowEnergy,integral_const_mul] using hh
  have hnonneg (n : ℕ) : 0 ≤ expectedFiniteLowEnergy (n := n) (k := k) (T := T)
      μ β Q θ e τ := integral_nonneg (fun _ => measureReal_nonneg)
  exact squeeze_zero hnonneg hbound (by simpa only [mul_zero] using hMean.const_mul (T:ℝ))

end SlowEquilibration.PureCapturePhysicalCoarseDiniLowEnergy
