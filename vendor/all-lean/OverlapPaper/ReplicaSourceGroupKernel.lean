module
public import OverlapPaper.ReplicaSourceTensorTilt
public import OverlapPaper.ReplicaSourceFiniteBranching

@[expose] public section

/-! Common Gaussian fields are sampled once per group and then copied to all
replicas in that group. Their normalized baseline tilt is an exact product of
actual scalar Cole--Hopf transitions, including zero mass and variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
open SpinGlass SpinGlass.Targets FourPapersCommon
open scoped BigOperators
namespace OverlapPaper

def replicaGroupCopy {g d : ℕ} (groupOf : Fin d → Fin g)
    (y : Fin g → ℝ) : Fin d → ℝ := fun l => y (groupOf l)

theorem measurable_replicaGroupCopy {g d : ℕ} (groupOf : Fin d → Fin g) :
    Measurable (replicaGroupCopy groupOf) := by
  unfold replicaGroupCopy
  fun_prop

def replicaGroupKernel {g d : ℕ} (κ : Kernel ℝ ℝ)
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  (replicaPiKernel g (fun j => κ.comap (fun x : Fin d → ℝ => x (representative j))
    (measurable_pi_apply _))).map (replicaGroupCopy groupOf)

theorem isMarkovKernel_replicaGroupKernel {g d : ℕ} (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] (groupOf : Fin d → Fin g) (representative : Fin g → Fin d) :
    IsMarkovKernel (replicaGroupKernel κ groupOf representative) := by
  haveI := isMarkovKernel_replicaPiKernel g
    (fun j => κ.comap (fun x : Fin d → ℝ => x (representative j)) (measurable_pi_apply _))
    (fun _ => inferInstance)
  exact Kernel.IsMarkovKernel.map _ (measurable_replicaGroupCopy groupOf)

theorem replicaGroupKernel_apply {g d : ℕ} (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (x : Fin d → ℝ) : replicaGroupKernel κ groupOf representative x =
      (Measure.pi (fun j => κ (x (representative j)))).map (replicaGroupCopy groupOf) := by
  rw [replicaGroupKernel, Kernel.map_apply _ (measurable_replicaGroupCopy groupOf),
    replicaPiKernel_apply g _ (fun _ => inferInstance)]
  rfl

theorem tilted_map_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (T : A → B) (hT : Measurable T) (f : B → ℝ)
    (hf : Measurable f) :
    (μ.map T).tilted f = (μ.tilted (fun x => f (T x))).map T := by
  ext s hs
  rw [Measure.map_apply hT hs, tilted_apply_eq_ofReal_integral' _ hs,
    tilted_apply_eq_ofReal_integral' _ (hT hs)]
  rw [integral_map hT.aemeasurable (hf.exp.aestronglyMeasurable)]
  congr 1
  exact setIntegral_map hs (by fun_prop) hT.aemeasurable

theorem constantMassKernel_eq_tilted (m : ℝ) (v : NNReal) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : ColeHopfFoundation.ProbabilityTheory.HasLinearGrowth A) (x : ℝ) :
    FRSB.constantMassKernel m v A x = (gaussianReal x v).tilted (fun y => m * A y) := by
  have hi := FRSB.integrable_constantMassWeight m v A hAg hAc.measurable x
  have he (y : ℝ) : Real.exp (m * A y) =
      Real.exp (m * coleHopf m v A x) * FRSB.constantMassWeight m v A x y := by
    rw [FRSB.constantMassWeight, ← Real.exp_add]
    congr 1
    ring
  have hI : (∫ y, Real.exp (m * A y) ∂gaussianReal x v) =
      Real.exp (m * coleHopf m v A x) := by
    simp_rw [he]
    rw [integral_const_mul, FRSB.integral_constantMassWeight m v A hAg hAc.measurable x,
      mul_one]
  rw [FRSB.constantMassKernel_apply m v A hAc hAg, FRSB.constantMassTransition,
    Measure.tilted]
  congr 1
  funext y
  rw [hI, FRSB.constantMassWeight, mul_sub, Real.exp_sub]

theorem replica_group_tilt_factorization {g d : ℕ}
    (μ : Fin g → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (hrep : ∀ j, groupOf (representative j) = j)
    (f : Fin g → ℝ → ℝ) (hf : ∀ j, Measurable (f j))
    (he : ∀ j, Integrable (fun y => Real.exp (f j y)) (μ j)) :
    ((Measure.pi μ).map (replicaGroupCopy groupOf)).tilted
        (fun y => ∑ j, f j (y (representative j))) =
      (Measure.pi (fun j => (μ j).tilted (f j))).map (replicaGroupCopy groupOf) := by
  rw [tilted_map_eq _ _ (measurable_replicaGroupCopy groupOf) _ (by fun_prop)]
  have hfun : (fun x : Fin g → ℝ => ∑ j, f j (replicaGroupCopy groupOf x (representative j))) =
      (fun x => ∑ j, f j (x j)) := by
    simp only [replicaGroupCopy, hrep]
  rw [hfun, tilted_pi_sum μ f hf he]


theorem mixed_replica_group_baseline_tilt {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ)
    (hp : p ≤ k + 1) (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (hrep : ∀ j, groupOf (representative j) = j) (x : Fin d → ℝ) :
    ((Measure.pi (fun j => gaussianReal (x (representative j))
      (ξ.first (s.q (p + 1)) - ξ.first (s.q p)).toNNReal)).map
        (replicaGroupCopy groupOf)).tilted
        (fun y => ∑ j, s.m p * mixedPotential ξ (Paper.parisiSchemeMeasure s)
          (s.q (p + 1), y (representative j))) =
      replicaGroupKernel (mixedSchemeScalarStep ξ s p) groupOf representative x := by
  have hb : s.q (p + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  haveI := isMarkovKernel_mixedSchemeScalarStep ξ s hp
  rw [replica_group_tilt_factorization _ groupOf representative hrep
    (fun _ y => s.m p * mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p + 1), y))
    (fun _ => (continuous_mixedPotential_section ξ _ _).measurable.const_mul _)
    (fun _ => ((mixedPotential_hasLinearGrowth ξ _ hb).exp_mul (s.m p)).integrable_gaussianReal
      (Real.continuous_exp.comp ((continuous_mixedPotential_section ξ _ _).const_mul (s.m p))).aestronglyMeasurable), replicaGroupKernel_apply]
  congr 2
  funext j
  exact (constantMassKernel_eq_tilted (s.m p) _ _
    (continuous_mixedPotential_section ξ _ _) (mixedPotential_hasLinearGrowth ξ _ hb)
    (x (representative j))).symm

end OverlapPaper
