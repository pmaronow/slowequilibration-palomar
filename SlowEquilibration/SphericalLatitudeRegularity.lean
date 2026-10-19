-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpatialRegularity

@[expose] public section

/-!
# Quantitative continuity of the genuine latitude partition

The affine latitude map is uniformly one-half Hölder even at the poles.
The resulting modulus for its actual log partition is explicit in the
actual tensor disorder norm and supports polynomial finite-grid estimates.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators InnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sqrt_sub_sq_le_abs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a-Real.sqrt b)^2 ≤ |a-b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) hna
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hba) hnb
    nlinarith

theorem latitude_scalar_chord_bound {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    (q-r)^2+(Real.sqrt (1-q^2)-Real.sqrt (1-r^2))^2 ≤ 4*|q-r| := by
  have hq' : 0 ≤ 1-q^2 := by nlinarith [abs_le.mp hq]
  have hr' : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hs := sqrt_sub_sq_le_abs hq' hr'
  have hd : |q-r| ≤ 2 := by
    exact (abs_sub q r).trans (by linarith)
  have hsum : |q+r| ≤ 2 := (abs_add_le q r).trans (by linarith)
  have he : |(1-q^2)-(1-r^2)| = |q-r| * |q+r| := by
    rw [show (1-q^2)-(1-r^2)=-(q-r)*(q+r) by ring,abs_mul,abs_neg]
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (q-r))
  have hd' := mul_le_mul_of_nonneg_left hd (abs_nonneg (q-r))
  nlinarith [sq_abs (q-r)]

/-- The exact latitude parametrization has a global Hölder modulus with
the correct square-root dimensional scale, including both poles. -/
theorem latitudeMap_dist_le {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    ‖latitudeMap u e q x-latitudeMap u e r x‖ ≤
      2*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt |q-r| := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let v : Vector (n+1) := Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)) • e x
  have hv : ‖v‖^2=((n+1 : ℕ) : ℝ) := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt (by positivity),e.norm_map,hx]
    field_simp
  have huv : inner ℝ u v=0 := by
    dsimp [v]
    rw [inner_smul_right,real_inner_comm,he,mul_zero]
  have hform (s : ℝ) : latitudeMap u e s x = s • u+Real.sqrt (1-s^2) • v := by
    unfold latitudeMap v
    rw [Real.sqrt_mul (by positivity),smul_smul]
    congr 1
    rw [mul_comm]
  have hdiff : latitudeMap u e q x-latitudeMap u e r x =
      (q-r) • u+(Real.sqrt (1-q^2)-Real.sqrt (1-r^2)) • v := by
    rw [hform q,hform r]
    module
  have hnorm : ‖latitudeMap u e q x-latitudeMap u e r x‖^2 =
      ((n+1 : ℕ) : ℝ)*((q-r)^2+(Real.sqrt (1-q^2)-Real.sqrt (1-r^2))^2) := by
    rw [hdiff,norm_add_sq_real,inner_smul_left,inner_smul_right,huv]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu,hv]
    ring
  have hh := mul_le_mul_of_nonneg_left (latitude_scalar_chord_bound hq hr)
    (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)
  have hb : ‖latitudeMap u e q x-latitudeMap u e r x‖^2 ≤
      (2*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt |q-r|)^2 := by
    rw [hnorm,mul_pow,mul_pow,Real.sq_sqrt (abs_nonneg _),Real.sq_sqrt (by positivity)]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

def latitudeModulus {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder (n+1) P) : ℝ :=
  2 * |β| * ‖euclideanDisorder J‖*Real.sqrt (spatialVariance c)*Real.sqrt ((n+1 : ℕ) : ℝ)

theorem latitudeModulus_nonneg {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder (n+1) P) : 0 ≤ latitudeModulus c β J := by unfold latitudeModulus; positivity

/-- Literal Hamiltonian continuity along the actual latitude parametrization. -/
theorem latitude_field_dist_le {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    |β*field c J (latitudeMap u e q x)-β*field c J (latitudeMap u e r x)| ≤
      latitudeModulus c β J*Real.sqrt |q-r| := by
  rw [← mul_sub,abs_mul]
  have hf := field_spatial_dist_le (by omega) c hc J
    (latitudeMap u e q x) (latitudeMap u e r x)
    (latitudeMap_norm_sq hn u hu e he hq x hx) (latitudeMap_norm_sq hn u hu e he hr x hx)
  have hm := mul_le_mul_of_nonneg_left (latitudeMap_dist_le hn u hu e he hq hr x hx)
    (mul_nonneg (norm_nonneg (euclideanDisorder J)) (Real.sqrt_nonneg (spatialVariance c)))
  have hh := mul_le_mul_of_nonneg_left (hf.trans hm) (abs_nonneg β)
  simpa only [latitudeModulus,mul_assoc,mul_left_comm,mul_comm] using hh

theorem latitudePartition_eq_sphereIntegral {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder (n+1) P) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    partitionAgainst (latitudeLaw u e q) β (field c J) =
      ∫ x, Real.exp (β*field c J (latitudeMap u e q x)) ∂sphereLaw n := by
  unfold partitionAgainst latitudeLaw
  apply integral_map (latitudeMap_continuous u e q).measurable.aemeasurable
  exact (Real.continuous_exp.comp (continuous_const.mul (field_contDiff c J).continuous)).aestronglyMeasurable

theorem latitudePartition_comparison {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    partitionAgainst (latitudeLaw u e q) β (field c J) ≤
      Real.exp (latitudeModulus c β J*Real.sqrt |q-r|)*
        partitionAgainst (latitudeLaw u e r) β (field c J) := by
  rw [latitudePartition_eq_sphereIntegral,latitudePartition_eq_sphereIntegral,← integral_const_mul]
  have hi (s : ℝ) : Integrable (fun x => Real.exp (β*field c J (latitudeMap u e s x))) (sphereLaw n) :=
    partition_integrand_integrable hn β
      ((field_contDiff c J).continuous.comp (latitudeMap_continuous u e s))
  apply integral_mono_ae (hi q) ((hi r).const_mul _)
  filter_upwards [sphereLaw_support hn] with x hx
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := (le_abs_self _).trans (latitude_field_dist_le hn c hc β J u hu e he hq hr x hx)
  linarith

def latitudeLogPartition {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (J : Disorder (n+1) P) : ℝ :=
  Real.log (partitionAgainst (latitudeLaw u e q) β (field c J))

theorem latitudeLogPartition_sub_le {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    latitudeLogPartition c β u e q J-latitudeLogPartition c β u e r J ≤
      latitudeModulus c β J*Real.sqrt |q-r| := by
  have hp (s : ℝ) (hs : |s| ≤ 1) : 0 < partitionAgainst (latitudeLaw u e s) β (field c J) :=
    partitionAgainst_pos _ ((latitudeLaw_support hn u hu e he hs).mono fun _ hv => hv.1)
      β (field_contDiff c J).continuous
  have hh := Real.log_le_log (hp q hq) (latitudePartition_comparison hn c hc β J u hu e he hq hr)
  rw [Real.log_mul (Real.exp_pos _).ne' (hp r hr).ne',Real.log_exp] at hh
  unfold latitudeLogPartition
  linarith

/-- The literal log partition has an explicit global Hölder bound under
the original tensor realization, including degenerate pole latitudes. -/
theorem latitudeLogPartition_dist_le {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    |latitudeLogPartition c β u e q J-latitudeLogPartition c β u e r J| ≤
      latitudeModulus c β J*Real.sqrt |q-r| := by
  apply abs_le.mpr
  constructor
  · have hh := latitudeLogPartition_sub_le hn c hc β J u hu e he hr hq
    rw [abs_sub_comm r q] at hh
    linarith
  · exact latitudeLogPartition_sub_le hn c hc β J u hu e he hq hr

end SlowEquilibration.SphericalModel
