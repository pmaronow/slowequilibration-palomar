-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagPhysicalDefinitions
public import Mathlib.MeasureTheory.Integral.Pi

/-! The product-Gibbs mass identity and pressure upper bound for the replicated
band in the proof of `prop:pc-replica-means` in Section 9 of the manuscript. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.ReplicaBandGibbsMass

open MeasureTheory SphericalModel LiteratureSubagPhysicalDefinitions
open scoped BigOperators
set_option autoImplicit false

private theorem band_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem product_density_integrable {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (fun σ : Fin k → Vector N => ∏ i, gibbsDensity N β H (σ i))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) :=
  Integrable.fintype_prod (fun _ => gibbsDensity_integrable hN β hH)

private theorem product_gibbs_eq_withDensity {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Measure.pi (fun _ : Fin k => gibbsLaw N β H) =
      (Measure.pi (fun _ : Fin k => sphereLaw N)).withDensity
        (fun σ => ENNReal.ofReal (∏ i, gibbsDensity N β H (σ i))) := by
  let := gibbsLaw_probability hN β hH
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))), Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      (gibbsDensity_pos hN β hH x).le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gibbsLaw, withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (gibbsDensity_integrable hN β hH).restrict
      (.of_forall (fun x => (gibbsDensity_pos hN β hH x).le))]

private theorem product_gibbs_real_eq_integral {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    {B : Set (Fin k → Vector N)} (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β H)).real B =
      ∫ σ in B, ∏ i, gibbsDensity N β H (σ i)
        ∂Measure.pi (fun _ : Fin k => sphereLaw N) := by
  rw [product_gibbs_eq_withDensity hN β hH, Measure.real,
    withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))),
    ENNReal.toReal_ofReal (integral_nonneg (fun σ =>
      Finset.prod_nonneg (fun i _ => (gibbsDensity_pos hN β hH (σ i)).le)))]

private theorem product_density_formula {N k : ℕ} (β : ℝ)
    (H : Vector N → ℝ) (m : Vector N) (σ : Fin k → Vector N) :
    (∏ i, gibbsDensity N β H (σ i)) =
      (Real.exp ((k : ℝ) * β * H m) / partition N β H ^ k) *
        Real.exp (β * ∑ i : Fin k, (H (σ i) - H m)) := by
  simp only [gibbsDensity, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

private theorem product_gibbs_band_mass {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (ReplicatedBand k q δ ρ m) =
      (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ k) * replicatedBandPartition k μ β q δ ρ J m := by
  rw [product_gibbs_real_eq_integral hN β (field_contDiff _ J).continuous
    (band_measurable q δ ρ m)]
  simp_rw [product_density_formula β (field (mixtureCoefficients μ) J) m]
  rw [integral_const_mul]
  rfl

/-- If the band has zero product surface measure, it has zero product Gibbs mass. -/
theorem productGibbs_band_eq_zero_of_volume_zero {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N)
    (h0 : (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k q δ ρ m) = 0) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
      (ReplicatedBand k q δ ρ m) = 0 := by
  rw [product_gibbs_eq_withDensity hN β (field_contDiff _ J).continuous]
  exact congrArg ENNReal.toReal (withDensity_absolutelyContinuous _ _ h0)

/-- The product Gibbs mass of a replicated band is controlled by any strict upper bound
for its replicated pressure. -/
theorem productGibbs_band_le {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) {A : ℝ}
    (hA : replicatedBandPressure k μ β q δ ρ J m < A) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (ReplicatedBand k q δ ρ m) ≤
      Real.exp ((N : ℝ) * (k : ℝ) *
        (β * field (mixtureCoefficients μ) J m / N + A -
          Real.log (mixturePartition μ β J) / N)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hkr : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hZ := mixturePartition_pos hN μ β J
  have hB : 0 ≤ replicatedBandPartition k μ β q δ ρ J m :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  rw [product_gibbs_band_mass hN μ β q δ ρ J m]
  by_cases hzero : replicatedBandPartition k μ β q δ ρ J m = 0
  · rw [hzero, mul_zero]
    exact (Real.exp_pos _).le
  have hBpos : 0 < replicatedBandPartition k μ β q δ ρ J m :=
    lt_of_le_of_ne hB (Ne.symm hzero)
  have hlog : Real.log (replicatedBandPartition k μ β q δ ρ J m) <
      (N : ℝ) * (k : ℝ) * A := by
    have hh := (div_lt_iff₀ (mul_pos hNr hkr)).mp hA
    simpa only [mul_comm A] using hh
  have hupper : replicatedBandPartition k μ β q δ ρ J m ≤
      Real.exp ((N : ℝ) * (k : ℝ) * A) := by
    rw [← Real.exp_log hBpos]
    exact (Real.exp_le_exp.mpr hlog.le)
  calc
    _ ≤ (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ k) * Real.exp ((N : ℝ) * (k : ℝ) * A) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = _ := by
      rw [← Real.exp_log hZ, ← Real.exp_nat_mul, div_mul_eq_mul_div,
        ← Real.exp_add, ← Real.exp_sub, Real.log_exp]
      congr 1
      field_simp [hNr.ne']

end SlowEquilibration.ReplicaBandGibbsMass
