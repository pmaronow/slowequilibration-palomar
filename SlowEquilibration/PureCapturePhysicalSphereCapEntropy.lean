-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeLaplace
public import SlowEquilibration.SphericalLatitudeNormalization

/-! Uniform near-one cap entropy for the original normalized spherical
surface law, obtained from proved spherical coarea and Gamma normalization. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalSphereCapEntropy
open SlowEquilibration SlowEquilibration.SphericalModel
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- A cap of latitude greater than `a` has exponentially small spherical
mass up to the actual Gamma-ratio prefactor. The axis is arbitrary. -/
theorem sphereLaw_near_one_cap_bound {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (sphereLaw (n+1)).real (overlapRegion u (Ioi a)) ≤
      4*Real.sqrt (n : ℝ)*(Real.sqrt (1-a^2))^(n-2) := by
  let t : ℝ := Real.sqrt (1-a^2)
  have harg : 0 < 1-a^2 := by nlinarith [ha, ha1]
  have ht : 0 < t := Real.sqrt_pos.mpr harg
  let M : ℝ := Real.log (t^(n-2))/((n+1 : ℕ) : ℝ)
  have he : Real.exp (((n+1 : ℕ) : ℝ)*M) = t^(n-2) := by
    dsimp [M]
    have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hc : (((n+1 : ℕ) : ℝ) *
        (Real.log (t^(n-2)) / ((n+1 : ℕ) : ℝ))) =
        Real.log (t^(n-2)) := by field_simp
    rw [hc]
    exact Real.exp_log (pow_pos ht _)
  have hupper : ∀ q ∈ Ioi a, q ∈ Ioo (-1 : ℝ) 1 →
      latitudeDensityPartition n 0 (fun _ : Vector (n+1) => 0) u q ≤
        Real.exp (((n+1 : ℕ) : ℝ)*M) := by
    intro q hqa hq
    rw [he]
    have hqa' : a < q := hqa
    have hmul : 0 ≤ (q-a)*(q+a) :=
      mul_nonneg (by linarith) (by linarith)
    have hsq : 1-q^2 ≤ 1-a^2 := by nlinarith
    have hsqrt : Real.sqrt (1-q^2) ≤ t := Real.sqrt_le_sqrt hsq
    have hpow : (Real.sqrt (1-q^2))^(n-2) ≤ t^(n-2) := by
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt _
    simpa [latitudeDensityPartition, partitionAgainst] using hpow
  have hpart := partitionOn_le_latitudeDensity_upper hn (0 : ℝ)
    (H := fun _ : Vector (n+1) => 0) continuous_const u hu
    measurableSet_Ioi hupper
  have hpart' : (sphereLaw (n+1)).real (overlapRegion u (Ioi a)) ≤
      4*(latitudeNormalization n).toReal*t^(n-2) := by
    have he' : Real.exp (((n : ℝ)+1)*M) = t^(n-2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using he
    simpa [partitionOn, Measure.real, he'] using hpart
  calc
    _ ≤ 4*(latitudeNormalization n).toReal*t^(n-2) := hpart'
    _ ≤ 4*Real.sqrt (n : ℝ)*t^(n-2) := by
      have hnrm := latitudeNormalization_toReal_le_sqrt (by omega : 1 ≤ n)
      nlinarith [pow_nonneg (Real.sqrt_nonneg (1-a^2)) (n-2)]

end SlowEquilibration.PureCapturePhysicalSphereCapEntropy
