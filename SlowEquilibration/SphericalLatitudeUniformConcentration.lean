-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePolynomialMesh

@[expose] public section

/-!
# Exponential concentration uniformly over the latitude continuum

The continuum estimate is proved for the literal tensor disorder by choosing
the concrete polynomial mesh. The true coordinate dimension and Gaussian
norm tail are accounted for, with no random regularity or uniformity premise.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine uniform concentration of all latitude log partitions. The
dimension threshold and exponential rate are uniform in the spherical center,
orthogonal frame, and latitude interval. -/
theorem latitude_uniform_concentration_eventually {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (a b : ℝ), -1 ≤ a → b ≤ 1 → a ≤ b →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) P {J | ∃ q ∈ Icc a b,
          ε*((n+1 : ℕ) : ℝ) ≤ |latitudeCenteredLogPartition c β u e q J|} ≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  let α : ℝ := (ε/2)^2/(2*β^2*covariancePolynomial c 1)
  have hα : 0 < α := by unfold α; positivity
  obtain ⟨γ,hγ,hγtail⟩ := latitude_polynomial_tail_eventually_le (2*(P+2)) hα
  let K : ℝ := 4 * |β| * Real.sqrt (spatialVariance c)*(2*((P+1 : ℕ) : ℝ)+1)
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hK : ∀ᶠ n : ℕ in atTop, K ≤ (ε/2)*((n+1 : ℕ) : ℝ) :=
    (hN.const_mul_atTop (by positivity : 0 < ε/2)).eventually (eventually_ge_atTop K)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hγtail,hK,eventually_ge_atTop 1] with n htail hK hn
  intro a b ha hb hab u hu e he
  have hmesh := latitude_uniform_concentration_finite_mesh hn (latitudeMeshSize_pos n P)
    c hc hcov hβ (show 0 < ε/2 by positivity) (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))
    ha hb hab u hu e he
  have herr := latitude_polynomial_mesh_error_le n P c β ha hb hab
  have hsubset : {J : Disorder (n+1) P | ∃ q ∈ Icc a b,
      ε*((n+1 : ℕ) : ℝ) ≤ |latitudeCenteredLogPartition c β u e q J|} ⊆
      {J : Disorder (n+1) P | ∃ q ∈ Icc a b,
        (ε/2)*((n+1 : ℕ) : ℝ)+latitudeModulusScale n c β*
          (2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+Real.sqrt ((n+1 : ℕ) : ℝ))*
            Real.sqrt ((b-a)/(latitudeMeshSize n P : ℝ)) ≤
              |latitudeCenteredLogPartition c β u e q J|} := by
    rintro J ⟨q,hq,hJ⟩
    refine ⟨q,hq,?_⟩
    change _ ≤ K at herr
    linarith
  have heα : -((ε/2)^2*((n+1 : ℕ) : ℝ))/(2*β^2*covariancePolynomial c 1) =
      -α*((n+1 : ℕ) : ℝ) := by unfold α; ring
  rw [Real.sq_sqrt (by positivity),heα] at hmesh
  apply ((measure_mono hsubset).trans hmesh).trans
  have hrhs : ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)/2))+
      ((latitudeMeshSize n P+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal (2*Real.exp (-α*((n+1 : ℕ) : ℝ))) =
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)/2)+
        2*((((n+1 : ℕ) : ℝ))^(2*(P+2))+1)*Real.exp (-α*((n+1 : ℕ) : ℝ))) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [latitudeMeshSize,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
    ring
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal htail

end SlowEquilibration.SphericalModel
