-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics
public import SlowEquilibration.SphericalQuenchedEndpoint

@[expose] public section

/-! Actual aligned linear fields and their deterministic latitude entropy
lower bounds. These supply the physical linear part of an external-field RS
bridge; no pressure limit or Parisi formula is assumed here. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem partitionOn_le_partition {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {B : Set (Vector N)} (hB : MeasurableSet B) :
    partitionOn β H B ≤ partition N β H := by
  rw [partitionOn,← integral_indicator hB]
  apply integral_mono ((partition_integrand_integrable hN β hH).indicator hB)
    (partition_integrand_integrable hN β hH)
  intro x
  by_cases hx : x ∈ B
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    exact (Real.exp_pos _).le

theorem linearSphereLogPartition_nonneg {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) (g : Vector N) :
    0 ≤ linearSphereLogPartition N κ g := by
  let : NeZero N := ⟨by omega⟩
  rw [linearSphereLogPartition,linearSphere_partition_eq_radius hN κ g]
  exact Real.log_nonneg (SphereLinear.partition_one_le g _)

def linearAxis (n : ℕ) (g : Vector (n+1)) : Vector (n+1) :=
  (Real.sqrt ((n+1 : ℕ) : ℝ)/‖g‖) • g

theorem linearAxis_norm_sq (n : ℕ) {g : Vector (n+1)} (hg : 0 < ‖g‖) :
    ‖linearAxis n g‖^2=((n+1 : ℕ) : ℝ) := by
  unfold linearAxis
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp

theorem linearAxis_alignment (n : ℕ) {g : Vector (n+1)} (hg : 0 < ‖g‖) :
    g=(‖g‖/Real.sqrt ((n+1 : ℕ) : ℝ)) • linearAxis n g := by
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((n+1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  unfold linearAxis
  rw [smul_smul,show ‖g‖/Real.sqrt ((n+1 : ℕ) : ℝ)*(Real.sqrt ((n+1 : ℕ) : ℝ)/‖g‖)=1 by field_simp,
    one_smul]

theorem linear_latitude_partition {n : ℕ} (hn : 1 ≤ n) (κ : ℝ)
    (g u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {σ q : ℝ}
    (hgu : g=σ • u) (hq : |q| ≤ 1) :
    partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) 1 (fun x => Real.sqrt κ*inner ℝ g x) =
      Real.exp (Real.sqrt κ*σ*((n+1 : ℕ) : ℝ)*q) := by
  have hs := latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hq
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold partitionAgainst
  calc
    _ = ∫ _x, Real.exp (Real.sqrt κ*σ*((n+1 : ℕ) : ℝ)*q)
        ∂latitudeLaw u (latitudeFrameAt u) q := by
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      rw [hgu,real_inner_smul_left,real_inner_comm x u]
      have hinner : inner ℝ x u=q*((n+1 : ℕ) : ℝ) := (div_eq_iff hN).mp hx.2
      rw [hinner,one_mul]
      congr 1
      ring
    _ = _ := by simp

theorem linear_latitude_profile {n : ℕ} (hn : 1 ≤ n) (κ : ℝ)
    (g u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {σ q : ℝ}
    (hgu : g=σ • u) (hq : |q| ≤ 1) :
    latitudePartitionProfile n 1 (fun x => Real.sqrt κ*inner ℝ g x) u q =
      Real.sqrt κ*σ*q+((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ))*Real.log (1-q^2) := by
  unfold latitudePartitionProfile
  rw [linear_latitude_partition hn κ g u hu hgu hq,Real.log_exp]
  congr 1
  field_simp

theorem latitude_entropy_coefficient_le_half (n : ℕ) :
    ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ)) ≤ 1/2 := by
  have hN : 0 < 2*((n+1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hN).mpr
  have hcast : ((n-2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 2
  simp only [Nat.cast_add,Nat.cast_one]
  linarith

theorem linear_latitude_profile_lower {n : ℕ} (hn : 1 ≤ n) (κ : ℝ)
    (g u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {σ s r w q : ℝ}
    (hgu : g=σ • u) (hs : 0 ≤ s) (hσ : s ≤ σ) (hw : 0 < w)
    (hrlo : 0 ≤ r-w) (hrhi : r+w < 1) (hq : q ∈ Icc (r-w) (r+w)) :
    Real.sqrt κ*s*(r-w)+Real.log (1-(r+w)^2)/2 ≤
      latitudePartitionProfile n 1 (fun x => Real.sqrt κ*inner ℝ g x) u q := by
  have hq0 : 0 ≤ q := hrlo.trans hq.1
  have hq1 : q < 1 := hq.2.trans_lt hrhi
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨by linarith,hq1.le⟩
  rw [linear_latitude_profile hn κ g u hu hgu hqa]
  have hlin : Real.sqrt κ*s*(r-w) ≤ Real.sqrt κ*σ*q := by
    have hsq := mul_le_mul hσ hq.1 hrlo (hs.trans hσ)
    have hh := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg κ)
    nlinarith
  have hr0 : 0 ≤ r+w := by linarith
  have harg : 0 < 1-(r+w)^2 := by nlinarith
  have hlog : Real.log (1-(r+w)^2) ≤ Real.log (1-q^2) :=
    Real.log_le_log harg (by nlinarith [hq.2])
  have hlogq : Real.log (1-q^2) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith [sq_nonneg q])
  have hc := mul_le_mul_of_nonpos_right (latitude_entropy_coefficient_le_half n) hlogq
  have he : Real.log (1-(r+w)^2)/2 ≤
      ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ))*Real.log (1-q^2) := by linarith
  linarith

end
end SlowEquilibration.SphericalModel
