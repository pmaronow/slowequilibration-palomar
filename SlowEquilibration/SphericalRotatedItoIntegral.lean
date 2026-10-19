-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRotationNoiseAlgebra
public import SphericalAging.FilteredItoPullback

/-! Deterministic coordinate mixing commutes with the constructed vector
Itô integral. The proof checks elementary predictable integrands first and
then uses their dense span in the actual predictable L² space. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.VectorIto
open FourPapersCommon.FilteredBrownian
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem coordinateIto_mixed_elementary
    (D E : BrownianDriver N P F) (A : Fin N → Fin N → ℝ)
    (hB : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => ∑ i : Fin N, A j i * D.coordinate i t ω)
    (j : Fin N) (s t : ℝ≥0) (hst : s ≤ t)
    (Z : lpMeas ℝ ℝ (F s) 2 P) :
    coordinateIto E j (elementaryPredictable F s t Z) =
      ∑ i : Fin N, A j i • coordinateIto D i (elementaryPredictable F s t Z) := by
  have hE : coordinateIto E j (elementaryPredictable F s t Z) =
      elementaryValue E j hst Z := by
    unfold coordinateIto elementaryValue
    rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable
      (hab := hst)]
  have hI (i : Fin N) : coordinateIto D i (elementaryPredictable F s t Z) =
      elementaryValue D i hst Z := by
    unfold coordinateIto elementaryValue
    rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable
      (hab := hst)]
  rw [hE]
  simp_rw [hI]
  apply Lp.ext
  have hD : ∀ᵐ ω ∂P, ∀ i : Fin N,
      (elementaryValue D i hst Z : Ω → ℝ) ω =
        (Z : Ω → ℝ) ω * increment D i s t ω :=
    ae_all_iff.mpr (fun i => elementaryValue_coe D i hst Z)
  have hSum := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin N))
    (fun i => A j i • elementaryValue D i hst Z)
  have hSmul : ∀ᵐ ω ∂P, ∀ i : Fin N,
      ((A j i • elementaryValue D i hst Z : RandomL2 P) : Ω → ℝ) ω =
        A j i * (elementaryValue D i hst Z : Ω → ℝ) ω :=
    ae_all_iff.mpr (fun i => by
      filter_upwards [Lp.coeFn_smul (A j i) (elementaryValue D i hst Z)]
        with ω hω
      simpa only [Pi.smul_apply,smul_eq_mul] using hω)
  filter_upwards [elementaryValue_coe E j hst Z,hD,hB j t,hB j s,hSum,hSmul]
    with ω hE hD ht hs hSum hSmul
  rw [hE,hSum]
  simp only [Finset.sum_apply]
  simp_rw [hSmul,hD]
  dsimp only [increment] at *
  rw [ht,hs]
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Actual Itô integrals against a linearly mixed Brownian coordinate equal
the corresponding linear combination of the original coordinate integrals. -/
theorem coordinateIto_mixed
    (D E : BrownianDriver N P F) (A : Fin N → Fin N → ℝ)
    (hB : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => ∑ i : Fin N, A j i * D.coordinate i t ω)
    (j : Fin N) (V : PredictableProcessL2 F P) :
    coordinateIto E j V = ∑ i : Fin N, A j i • coordinateIto D i V := by
  let L := coordinateIto E j
  let R : PredictableProcessL2 F P →L[ℝ] RandomL2 P :=
    ∑ i : Fin N, A j i • coordinateIto D i
  suffices h : L V=R V by simpa only [L,R, sum_apply, smul_apply] using h
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable
      (P := P) F).induction_on V
    (isClosed_eq L.continuous R.continuous) ?_
  intro v
  have hv : FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable F P v =
      ∑ q ∈ v.support, v q •
        FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P q := by
    simp only [FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable,
      Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hv, map_sum, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  simp only [L,R,FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator,
    sum_apply,smul_apply]
  exact coordinateIto_mixed_elementary D E A hB j q.1 q.2.1.1 q.2.1.2 q.2.2

end SlowEquilibration.SphericalRotationCovariance
