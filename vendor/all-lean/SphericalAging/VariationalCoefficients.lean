module

public import SphericalAging.PredictableLinearCoefficient
public import SphericalAging.RandomInitialSphere

public section

/-! True fderiv coefficients of the stochastic variational equation. Their
predictability is constructed from the actual adapted continuous state,
and their operator norm bounds follow from genuine cutoff Lipschitzness. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.VariationalCoefficients
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def coordinate (i : Fin N) : State N →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin N => ℝ) i

@[simp] theorem coordinate_apply (i : Fin N) (x : State N) : coordinate i x = x i := rfl

theorem scalar_fderiv_coordinates (g : State N → ℝ) (x v : State N) :
    fderiv ℝ g x v = ∑ i : Fin N, (fderiv ℝ g x (basisVector i)) * v i := by
  conv_lhs => rw [← state_sum_basis v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,smul_eq_mul,mul_comm]

theorem cutoffDrift_contDiff (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (i : Fin N) :
    ContDiff ℝ ∞ (CutoffSDE.cutoffDrift β J R hR i) :=
  (coordinate i).contDiff.comp (cutoffCoefficient_contDiff R hR _
    ((contDiff_hamiltonianDrift β J).of_le (by simp)))

theorem cutoffNoise_contDiff (R : ℝ) (hR : 0 < R) (i j : Fin N) :
    ContDiff ℝ ∞ (CutoffSDE.cutoffNoise N R hR i j) :=
  (coordinate i).contDiff.comp (cutoffCoefficient_contDiff R hR _
    ((contDiff_noiseColumn j).of_le (by simp)))

theorem derivative_timeCut_predictable (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (g : State N → ℝ) (hg : ContDiff ℝ ∞ g) (T : ℝ≥0) :
    AEStronglyMeasurable[F.predictable]
      (fun q : ℝ≥0 × Ω => if q.1 ∈ Ioc 0 T then fderiv ℝ g (X q.1 q.2) else 0)
      (nonnegativeLebesgueMeasure.prod P) := by
  classical
  have hc (i : Fin N) : Continuous (fun x : State N => fderiv ℝ g x (basisVector i)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi (i : Fin N) := FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
    (fun t omega => fderiv ℝ g (X t omega) (basisVector i))
    (fun t => (hc i).comp_stronglyMeasurable (hXa t))
    (hXc.mono (fun omega homega => (hc i).comp homega)) T
  have hsum : AEStronglyMeasurable[F.predictable]
      (fun q : ℝ≥0 × Ω => ∑ i : Fin N, FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => fderiv ℝ g (X t omega) (basisVector i)) T q • coordinate i)
      (nonnegativeLebesgueMeasure.prod P) :=
    by
      suffices hs : ∀ s : Finset (Fin N), AEStronglyMeasurable[F.predictable]
          (fun q : ℝ≥0 × Ω => ∑ i ∈ s, FourPapersCommon.continuousAdaptedTimeCut
            (fun t omega => fderiv ℝ g (X t omega) (basisVector i)) T q • coordinate i)
          (nonnegativeLebesgueMeasure.prod P) from hs Finset.univ
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (aestronglyMeasurable_const (m := F.predictable)
          (μ := nonnegativeLebesgueMeasure.prod P) (b := (0 : State N →L[ℝ] ℝ)))
      | @insert i s his ih =>
        simpa only [Finset.sum_insert his] using
          continuous_add.comp_aestronglyMeasurable (((hi i).smul_const (coordinate i)).prodMk ih)
  apply hsum.congr
  apply Filter.Eventually.of_forall
  intro q
  apply ContinuousLinearMap.ext
  intro v
  by_cases ht : q.1 ∈ Ioc 0 T
  · simp only [ht,ite_true,sum_apply,smul_apply,
      coordinate_apply,smul_eq_mul,FourPapersCommon.continuousAdaptedTimeCut]
    exact (scalar_fderiv_coordinates g (X q.1 q.2) v).symm
  · simp [ht,FourPapersCommon.continuousAdaptedTimeCut]

/-- Constructed bounded predictable derivative row, retaining the actual
Fréchet derivative rather than introducing a formal Jacobian symbol. -/
@[expose] def derivativeRow (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g) (T : ℝ≥0) :
    Coefficient (N := N) (F := F) (P := P) K where
  value q := if q.1 ∈ Ioc 0 T then fderiv ℝ g (X q.1 q.2) else 0
  measurable := derivative_timeCut_predictable X hXa hXc g hg T
  bound := .of_forall (fun q => by
    by_cases ht : q.1 ∈ Ioc 0 T
    · simp only [ht,ite_true]
      exact norm_fderiv_le_of_lipschitz ℝ hL
    · simp only [ht,ite_false,norm_zero]
      exact K.coe_nonneg)

end SphericalAging.VariationalCoefficients
