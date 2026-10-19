-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeMesh
public import SlowEquilibration.GaussianNormConcentration

@[expose] public section

/-!
# Actual finite-grid concentration for all latitudes

The random regularity bound is controlled by the true Gaussian coefficient
norm with exponential failure probability. Pointwise concentration on the
literal finite mesh then controls the entire continuum of latitude log
partitions, including the poles.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeModulusScale (n : ℕ) {P : ℕ} (c : Degree P → ℝ) (β : ℝ) : ℝ :=
  2 * |β| * Real.sqrt (spatialVariance c)*Real.sqrt ((n+1 : ℕ) : ℝ)

theorem latitudeModulusScale_nonneg (n : ℕ) {P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    0 ≤ latitudeModulusScale n c β := by unfold latitudeModulusScale; positivity

theorem latitudeModulus_eq {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder (n+1) P) :
    latitudeModulus c β J = latitudeModulusScale n c β*‖euclideanDisorder J‖ := by
  unfold latitudeModulus latitudeModulusScale
  ring

theorem euclideanDisorder_norm_integrable (N P : ℕ) :
    Integrable (fun J : Disorder N P => ‖euclideanDisorder J‖) (disorderLaw N P) := by
  exact (euclideanDisorder_hasLaw N P).integrable_comp GaussianSpinInterpolation.gaussian_norm_integrable

theorem euclideanDisorder_norm_integral_le (N P : ℕ) :
    (∫ J : Disorder N P, ‖euclideanDisorder J‖ ∂disorderLaw N P) ≤
      Real.sqrt (Fintype.card (Coordinate N P) : ℝ) := by
  have he := (euclideanDisorder_hasLaw N P).integral_comp
    (f := fun g : EuclideanDisorder N P => ‖g‖) (by fun_prop)
  dsimp only [Function.comp_apply] at he
  rw [he]
  exact GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card _

theorem euclideanDisorder_norm_upper_tail (N P : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    disorderLaw N P {J | Real.sqrt (Fintype.card (Coordinate N P) : ℝ)+s ≤ ‖euclideanDisorder J‖} ≤
      ENNReal.ofReal (Real.exp (-s^2/2)) := by
  have h := GaussianNormConcentration.standardGaussian_norm_upper_tail (ι := Coordinate N P) hs
  have hlaw := euclideanDisorder_hasLaw N P
  rw [← hlaw.map_eq,Measure.map_apply_of_aemeasurable hlaw.aemeasurable
    (measurableSet_le measurable_const (by fun_prop))] at h
  exact h

theorem latitudeLogPartition_integrable {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β : ℝ} (hβ : 0 < β) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    Integrable (latitudeLogPartition c β u e q) (disorderLaw (n+1) P) :=
  logPartitionAgainst_disorder_integrable (by omega) _
    ((latitudeLaw_support hn u hu e he hq).mono fun _ hv => hv.1) c hc hcov hβ

theorem latitudeMeanLogPartition_sub_le {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β : ℝ} (hβ : 0 < β) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    (∫ J, latitudeLogPartition c β u e q J ∂disorderLaw (n+1) P)-
      (∫ J, latitudeLogPartition c β u e r J ∂disorderLaw (n+1) P) ≤
      latitudeModulusScale n c β*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)*Real.sqrt |q-r| := by
  rw [← integral_sub (latitudeLogPartition_integrable hn c hc hcov hβ u hu e he hq)
    (latitudeLogPartition_integrable hn c hc hcov hβ u hu e he hr)]
  calc
    _ ≤ ∫ J : Disorder (n+1) P,
        latitudeModulusScale n c β*‖euclideanDisorder J‖*Real.sqrt |q-r| ∂disorderLaw (n+1) P := by
      apply integral_mono
        ((latitudeLogPartition_integrable hn c hc hcov hβ u hu e he hq).sub
          (latitudeLogPartition_integrable hn c hc hcov hβ u hu e he hr))
        (((euclideanDisorder_norm_integrable (n+1) P).const_mul _).mul_const _)
      intro J
      change latitudeLogPartition c β u e q J-latitudeLogPartition c β u e r J ≤ _
      simpa only [latitudeModulus_eq] using latitudeLogPartition_sub_le hn c hc β J u hu e he hq hr
    _ ≤ _ := by
      rw [integral_mul_const,integral_const_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (euclideanDisorder_norm_integral_le (n+1) P)
          (latitudeModulusScale_nonneg n c β)) (Real.sqrt_nonneg _)

def latitudeCenteredLogPartition {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (J : Disorder (n+1) P) : ℝ :=
  latitudeLogPartition c β u e q J-
    ∫ K, latitudeLogPartition c β u e q K ∂disorderLaw (n+1) P

theorem latitudeCenteredLogPartition_dist_le {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β : ℝ} (hβ : 0 < β) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    |latitudeCenteredLogPartition c β u e q J-latitudeCenteredLogPartition c β u e r J| ≤
      latitudeModulusScale n c β*(‖euclideanDisorder J‖+
        Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ))*Real.sqrt |q-r| := by
  have hf := latitudeLogPartition_dist_le hn c hc β J u hu e he hq hr
  rw [latitudeModulus_eq] at hf
  have hm := latitudeMeanLogPartition_sub_le hn c hc hcov hβ u hu e he hq hr
  have hm' := latitudeMeanLogPartition_sub_le hn c hc hcov hβ u hu e he hr hq
  rw [abs_sub_comm r q] at hm'
  apply abs_le.mpr
  unfold latitudeCenteredLogPartition
  constructor <;> nlinarith [abs_le.mp hf]

/-- A genuine finite-dimensional concentration inequality for the complete
latitude continuum. Every term on the right is explicit: one actual Gaussian
norm tail and k+1 ordinary latitude concentration tails. -/
theorem latitude_uniform_concentration_finite_mesh {n P k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β t s a b : ℝ} (hβ : 0 < β) (ht : 0 < t) (hs : 0 ≤ s)
    (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0) :
    disorderLaw (n+1) P {J | ∃ q ∈ Icc a b,
      t*((n+1 : ℕ) : ℝ)+latitudeModulusScale n c β*
        (2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+s)*Real.sqrt ((b-a)/(k : ℝ)) ≤
          |latitudeCenteredLogPartition c β u e q J|} ≤
      ENNReal.ofReal (Real.exp (-s^2/2))+
        ((k+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal
          (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*β^2*covariancePolynomial c 1))) := by
  classical
  let A : Set (Disorder (n+1) P) :=
    {J | Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+s ≤ ‖euclideanDisorder J‖}
  let B : Fin (k+1) → Set (Disorder (n+1) P) := fun i =>
    {J | t*((n+1 : ℕ) : ℝ) ≤ |latitudeCenteredLogPartition c β u e (latitudeMeshPoint k a b i) J|}
  have hsub : {J | ∃ q ∈ Icc a b,
      t*((n+1 : ℕ) : ℝ)+latitudeModulusScale n c β*
        (2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+s)*Real.sqrt ((b-a)/(k : ℝ)) ≤
          |latitudeCenteredLogPartition c β u e q J|} ⊆ A ∪ ⋃ i, B i := by
    intro J hJ
    rcases hJ with ⟨q,hq,hJ⟩
    by_cases hA : J ∈ A
    · exact Or.inl hA
    right
    by_contra hB
    have hnorm : ‖euclideanDisorder J‖ < Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+s :=
      lt_of_not_ge hA
    obtain ⟨i,hi⟩ := latitudeMeshPoint_covers hk hab hq
    have hiI := latitudeMeshPoint_mem hk hab i
    have hqabs : |q| ≤ 1 := abs_le.mpr ⟨ha.trans hq.1,hq.2.trans hb⟩
    have hiabs : |latitudeMeshPoint k a b i| ≤ 1 := abs_le.mpr ⟨ha.trans hiI.1,hiI.2.trans hb⟩
    have hgrid : |latitudeCenteredLogPartition c β u e (latitudeMeshPoint k a b i) J| <
        t*((n+1 : ℕ) : ℝ) := by
      apply lt_of_not_ge
      intro h
      exact hB (mem_iUnion.mpr ⟨i,h⟩)
    have hd := latitudeCenteredLogPartition_dist_le hn c hc hcov hβ J u hu e he hqabs hiabs
    have hm : latitudeModulusScale n c β*(‖euclideanDisorder J‖+
        Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ))*
          Real.sqrt |q-latitudeMeshPoint k a b i| ≤
        latitudeModulusScale n c β*(2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+s)*
          Real.sqrt ((b-a)/(k : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) (latitudeModulusScale_nonneg n c β)
      · exact Real.sqrt_le_sqrt hi
      · positivity
      · exact mul_nonneg (latitudeModulusScale_nonneg n c β) (by positivity)
    have htri := abs_add_le
      (latitudeCenteredLogPartition c β u e q J-
        latitudeCenteredLogPartition c β u e (latitudeMeshPoint k a b i) J)
      (latitudeCenteredLogPartition c β u e (latitudeMeshPoint k a b i) J)
    rw [sub_add_cancel] at htri
    linarith
  have hA := euclideanDisorder_norm_upper_tail (n+1) P hs
  have hB (i : Fin (k+1)) : disorderLaw (n+1) P (B i) ≤
      ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*β^2*covariancePolynomial c 1))) := by
    have hi := latitudeMeshPoint_mem hk hab i
    exact logPartitionAgainst_pressure_concentration (by omega) _
      ((latitudeLaw_support hn u hu e he (abs_le.mpr ⟨ha.trans hi.1,hi.2.trans hb⟩)).mono fun _ hv => hv.1)
      c hc hcov hβ ht
  calc
    _ ≤ disorderLaw (n+1) P (A ∪ ⋃ i, B i) := measure_mono hsub
    _ ≤ disorderLaw (n+1) P A+∑ i, disorderLaw (n+1) P (B i) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ ENNReal.ofReal (Real.exp (-s^2/2))+
        ∑ _i : Fin (k+1), ENNReal.ofReal
          (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*β^2*covariancePolynomial c 1))) :=
      add_le_add hA (Finset.sum_le_sum fun i _ => hB i)
    _ = _ := by simp

end SlowEquilibration.SphericalModel
