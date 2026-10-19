-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalCoarseLimit

/-! Borel status of the literal physical finite-ensemble score and
low-energy events from source Proposition 9.16, and their disorder-averaged
probabilities under the original Gibbs kernel. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFiniteMeasurability

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalBarycenter MixedCaptureReplicaGeometry
open PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The source overlap with a pair of physical spins is jointly continuous. -/
theorem overlap_joint_continuous {N : ℕ} :
    Continuous (fun p : Vector N × Vector N => overlap p.1 p.2) := by
  unfold overlap
  exact (continuous_fst.inner continuous_snd).div_const _

/-- Strict overlap constraints on one query and a fixed companion block
form an open set in the actual physical spin coordinates. -/
theorem goodCompanionBlock_open {N k : ℕ} (Q θ : ℝ) :
    IsOpen {p : Vector N × (Fin k → Vector N) |
      goodCompanionBlock Q θ p.1 p.2} := by
  have hpair : IsOpen {p : Vector N × (Fin k → Vector N) |
      ∀ i j : Fin k, i ≠ j → |overlap (p.2 i) (p.2 j) - Q| < θ} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    by_cases hij : i = j
    · simp [hij]
    · have hmap : Continuous (fun p : Vector N × (Fin k → Vector N) =>
          ((p.2 i),(p.2 j))) :=
        ((continuous_apply i).comp continuous_snd).prodMk
          ((continuous_apply j).comp continuous_snd)
      have hopen : IsOpen {p : Vector N × (Fin k → Vector N) |
          |overlap (p.2 i) (p.2 j)-Q| < θ} :=
        isOpen_lt ((overlap_joint_continuous.comp hmap).sub continuous_const).abs
          continuous_const
      simpa only [hij, ne_eq, not_false_eq_true, iInter_true] using hopen
  have hquery : IsOpen {p : Vector N × (Fin k → Vector N) |
      ∀ i : Fin k, |overlap p.1 (p.2 i)-Q| < θ} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hmap : Continuous (fun p : Vector N × (Fin k → Vector N) =>
        (p.1,p.2 i)) :=
      continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
    exact isOpen_lt ((overlap_joint_continuous.comp hmap).sub continuous_const).abs
      continuous_const
  simpa only [goodCompanionBlock, Set.ofPred_and] using hpair.inter hquery

theorem allBlocksFail_measurable {N k T : ℕ} (Q θ : ℝ) :
    MeasurableSet (allBlocksFail (N := N) (k := k) (T := T) Q θ) := by
  have hblock (b : Fin T) :
      MeasurableSet {p : PhysicalEnsemble N k T |
        ¬goodCompanionBlock Q θ p.1 (p.2 b)} := by
    have hmap : Measurable (fun p : PhysicalEnsemble N k T => (p.1,p.2 b)) :=
      measurable_fst.prodMk ((measurable_pi_apply b).comp measurable_snd)
    have hG : MeasurableSet {q : Vector N × (Fin k → Vector N) |
        goodCompanionBlock Q θ q.1 q.2} :=
      (goodCompanionBlock_open Q θ).measurableSet
    exact hG.compl.preimage hmap
  unfold allBlocksFail
  change MeasurableSet {p : PhysicalEnsemble N k T |
    ∀ b : Fin T, ¬goodCompanionBlock Q θ p.1 (p.2 b)}
  convert MeasurableSet.iInter hblock using 1
  ext p
  simp

/-- The literal physical normalized mean remains Borel even when an
arbitrary off-sphere tuple has zero empirical mean. -/
theorem physicalTrainingCenter_measurable {N k : ℕ} :
    Measurable (physicalTrainingCenter (N := N) (n := k)) := by
  have hspin : Measurable (fun σ : Fin k → Vector N => fun i => spin (σ i)) := by
    apply Measurable.of_eval
    intro i
    exact spin_contDiff.continuous.measurable.comp (measurable_pi_apply i)
  have hmean : Measurable (fun σ : Fin k → Vector N =>
      replicaMean (fun i => spin (σ i))) := by
    change Measurable (fun σ : Fin k → Vector N =>
      (k : ℝ)⁻¹ • ∑ i, spin (σ i))
    exact (Finset.measurable_sum (Finset.univ : Finset (Fin k)) (fun i _ =>
      spin_contDiff.continuous.measurable.comp (measurable_pi_apply i))).const_smul
        ((k : ℝ)⁻¹)
  unfold physicalTrainingCenter normalizedReplicaMean
  exact (hmean.norm.inv.smul hmean).const_smul (Real.sqrt (N : ℝ))

/-- Genuine conditional Gibbs kernel for one query and independent
companion blocks, before any disorder averaging. -/
def physicalEnsembleKernel {n k T : ℕ} (μ : FiniteMixture) (β : ℝ) :
    Kernel (Disorder (n+2) μ.maxDegree) (PhysicalEnsemble (n+2) k T) :=
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  G ×ₖ GaussianReplicaKernel.iid (GaussianReplicaKernel.iid G k) T

instance physicalEnsembleKernel_markov {n k T : ℕ} (μ : FiniteMixture) (β : ℝ) :
    IsMarkovKernel (physicalEnsembleKernel (n := n) (k := k) (T := T) μ β) := by
  unfold physicalEnsembleKernel
  infer_instance

theorem physicalEnsembleKernel_apply {n k T : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder (n+2) μ.maxDegree) :
    physicalEnsembleKernel (k := k) (T := T) μ β J =
      physicalEnsembleLaw (k := k) (T := T) μ β J := by
  unfold physicalEnsembleKernel physicalEnsembleLaw
  rw [Kernel.prod_apply, GaussianReplicaKernel.iid_apply]
  simp_rw [GaussianReplicaKernel.iid_apply,allDimensionGibbsKernel_apply]

/-- For fixed disorder, the physical score-failure probability is a
measurable function of that disorder. -/
theorem finiteFailureProbability_measurable {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) :
    Measurable (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (allBlocksFail Q θ)) := by
  convert
    ((physicalEnsembleKernel (n := n) (k := k) (T := T) μ β).measurable_coe
      (allBlocksFail_measurable Q θ)).ennreal_toReal
  rw [Measure.real,physicalEnsembleKernel_apply]

end SlowEquilibration.PureCapturePhysicalFiniteMeasurability
