-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalLocalSolutionPullback
public import SlowEquilibration.SphericalRotationNoiseAlgebra

/-! Finite-dimensional covariance identities for the actual predictable
coefficient classes of the physical spherical SDE. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalModel
open Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {N : ℕ}

theorem rotated_coordinate_sum (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (v : Vector N) (k : Fin N) :
    (U v) k = ∑ i : Fin N, (U (basisVector i)) k * v i := by
  conv_lhs => rw [← state_sum_basis v]
  rw [map_sum]
  simp [map_smul, Finset.sum_apply, smul_eq_mul, mul_comm]

theorem noiseColumn_rotated_double_sum (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (v : Vector N) (j k : Fin N) :
    (∑ i : Fin N, (U (basisVector i)) k * (noiseColumn v j) i) =
      ∑ l : Fin N, (U (basisVector j)) l * (noiseColumn (U v) l) k := by
  rw [← rotated_coordinate_sum U (noiseColumn v j) k]
  exact (noiseColumn_rotated_matrix U v j k).symm

section Predictable
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
theorem coefficientTimeCut_finsetLinear_memLp
    (X : ℝ≥0 → Ω → State N)
    (g : Fin N → State N → ℝ) (G : State N → ℝ)
    (c : Fin N → ℝ) (hG : ∀ x, G x = ∑ i, c i * g i x)
    (t : ℝ≥0)
    (hm : ∀ i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => g i (X s ω)) t) 2
      (nonnegativeLebesgueMeasure.prod P)) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => G (X s ω)) t) 2
      (nonnegativeLebesgueMeasure.prod P) := by
  have hcut : FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => G (X s ω)) t =
      ∑ i : Fin N, c i • FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => g i (X s ω)) t := by
    funext z
    by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) t
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact hG (X z.1 z.2)
    · simp [FourPapersCommon.continuousAdaptedTimeCut,ht]
  rw [hcut]
  exact memLp_finsetSum' Finset.univ
    (fun i _ => (hm i).const_smul (c i))

theorem coefficientPredictableActual_finsetLinear
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (g : Fin N → State N → ℝ) (G : State N → ℝ)
    (hg : ∀ i, Continuous (g i)) (hGcont : Continuous G)
    (c : Fin N → ℝ) (hG : ∀ x, G x = ∑ i, c i * g i x)
    (t : ℝ≥0)
    (hm : ∀ i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => g i (X s ω)) t) 2
      (nonnegativeLebesgueMeasure.prod P)) :
    coefficientPredictableActual hXa hXc hGcont t
        (coefficientTimeCut_finsetLinear_memLp X g G c hG t hm) =
      ∑ i : Fin N, c i • coefficientPredictableActual hXa hXc (hg i) t (hm i) := by
  apply Subtype.ext
  apply Lp.ext
  have hall : ∀ᵐ z ∂nonnegativeLebesgueMeasure.prod P,
      ∀ i : Fin N,
        (c i • (coefficientPredictableActual hXa hXc (hg i) t (hm i) :
          TimeProcessL2 P)) z =
        c i * FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => g i (X s ω)) t z := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (c i)
      (coefficientPredictableActual hXa hXc (hg i) t (hm i) : TimeProcessL2 P),
      (hm i).coeFn_toLp] with z hs hc
    change (coefficientPredictableActual hXa hXc (hg i) t (hm i) : TimeProcessL2 P) z = _ at hc
    rw [hs, Pi.smul_apply, hc, smul_eq_mul]
  filter_upwards [(coefficientTimeCut_finsetLinear_memLp X g G c hG t hm).coeFn_toLp,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin N =>
      c i • (coefficientPredictableActual hXa hXc (hg i) t (hm i) : TimeProcessL2 P)),
    hall] with z hleft hsum hall
  change (coefficientPredictableActual hXa hXc hGcont t
      (coefficientTimeCut_finsetLinear_memLp X g G c hG t hm) : TimeProcessL2 P) z =
    ((∑ i : Fin N, c i • coefficientPredictableActual hXa hXc (hg i) t (hm i) :
      PredictableProcessL2 F P) : TimeProcessL2 P) z
  change (coefficientPredictableActual hXa hXc hGcont t
    (coefficientTimeCut_finsetLinear_memLp X g G c hG t hm) : TimeProcessL2 P) z =
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => G (X s ω)) t z at hleft
  rw [hleft]
  have hcast :
      ((∑ i : Fin N, c i • coefficientPredictableActual hXa hXc (hg i) t (hm i) :
          PredictableProcessL2 F P) : TimeProcessL2 P) =
        ∑ i : Fin N, c i •
          (coefficientPredictableActual hXa hXc (hg i) t (hm i) : TimeProcessL2 P) := by
    change (PredictableProcessL2 F P).subtypeL
      (∑ i : Fin N, c i • coefficientPredictableActual hXa hXc (hg i) t (hm i)) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hcast]
  rw [hsum]
  by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) t
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true] at hall ⊢
    rw [hG]
    simp only [Finset.sum_apply]
    exact (Finset.sum_congr rfl (fun i _ => hall i)).symm
  · simp [FourPapersCommon.continuousAdaptedTimeCut,ht,hall]

end Predictable

end SlowEquilibration.SphericalRotationCovariance
