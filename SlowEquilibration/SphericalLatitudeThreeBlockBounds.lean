-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeThreeBlock
public import SlowEquilibration.SphericalLatitudeNegativeTangent

@[expose] public section

/-! # Actual odd-mixture three-block covariance bounds

The physical signed covariance kernel admits a uniform bound by its RS
supporting line and a fixed negative-transverse-overlap indicator. The
held perturbation bank cancels exactly, with no positivity premise.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The true finite latitude RS pair-covariance level. -/
def latitudeRSPairLevel (n : ℕ) (μ : FiniteMixture) (β q : ℝ) : ℝ :=
  β^2*((n+1 : ℕ) : ℝ)*((q-q^2)*μ.xi1 q-μ.xi q)

/-- The signed covariance error is exactly the literal covariance tangent
 deficit, independently of all perturbation coordinates. -/
theorem latitudeThree_signedKernel_sub_pairLevel (hn : 1 ≤ n) (μ : FiniteMixture)
    (β : ℝ) {q : ℝ} (hq : q ∈ Icc 0 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    (W : Vector n → EuclideanSpace ℝ ι) (x y : Vector n) :
    GaussianThreeBlockComparison.signedKernel
      (latitudeThreeLinear (mixtureCoefficients μ) β (latitudeLinearVariance n μ β q) u e q W)
      latitudeThreeLabel x y-latitudeRSPairLevel n μ β q =
        β^2*((n+1 : ℕ) : ℝ)*latitudeTangentDeficit μ q (overlap x y) := by
  rw [latitudeThree_signedKernel hn _ (mixtureCoefficients_nonnegative μ) β
    (latitudeLinearVariance_nonneg n μ β hq) u hu e he
    (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩),covariancePolynomial_mixture,
    latitudeLinearVariance_mul_dim hn μ β q]
  unfold latitudeRSPairLevel latitudeTangentDeficit
  ring

/-- The diagonal kernel is the actual original-minus-trial variance level
on the tangent sphere, for every held perturbation bank. -/
theorem latitudeThree_signedKernel_diagonal (hn : 1 ≤ n) (μ : FiniteMixture)
    (β : ℝ) {q : ℝ} (hq : q ∈ Icc 0 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    (W : Vector n → EuclideanSpace ℝ ι) (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    GaussianThreeBlockComparison.signedKernel
      (latitudeThreeLinear (mixtureCoefficients μ) β (latitudeLinearVariance n μ β q) u e q W)
      latitudeThreeLabel x x = latitudeLinearVariance n μ β q*(n : ℝ)-
        β^2*((n+1 : ℕ) : ℝ)*μ.xi 1 := by
  rw [latitudeThree_signedKernel hn _ (mixtureCoefficients_nonnegative μ) β
    (latitudeLinearVariance_nonneg n μ β hq) u hu e he
    (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩),overlap_self (by omega) x hx,
    covariancePolynomial_mixture]
  rw [show q^2+(1-q^2)*(1 : ℝ)=1 by ring,mul_one]

/-- The finite error cutoff and constant are chosen before dimension,
Gaussian realization, latitude, frame and held perturbation bank. -/
theorem exists_uniform_latitudeThree_signedKernel_bound (μ : FiniteMixture) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ < 1) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ (n : ℕ),1 ≤ n → ∀ (β q : ℝ),q∈Icc δ ρ →
      ∀ (u : Vector (n+1)),‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),(∀ x,inner ℝ (e x) u=0) →
      ∀ (W : Vector n → EuclideanSpace ℝ ι) (x y : Vector n),
      ‖x‖^2=(n : ℝ) → ‖y‖^2=(n : ℝ) →
      GaussianThreeBlockComparison.signedKernel
        (latitudeThreeLinear (mixtureCoefficients μ) β (latitudeLinearVariance n μ β q) u e q W)
        latitudeThreeLabel x y ≤ latitudeRSPairLevel n μ β q+
          (β^2*((n+1 : ℕ) : ℝ)*C)*
            ({z : Vector n × Vector n | overlap z.1 z.2 < -η}.indicator (fun _ => (1 : ℝ))) (x,y) := by
  obtain ⟨η,C,hη,hη1,hC,hbound⟩ := exists_uniform_latitude_tangent_deficit_bound μ hδ hδρ hρ
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro n hn β q hq u hu e he W x y hx hy
  have hq01 : q∈Icc (0 : ℝ) 1 := ⟨hδ.le.trans hq.1,hq.2.trans hρ.le⟩
  have hh := mul_le_mul_of_nonneg_left
    (hbound q hq (overlap x y) (overlap_mem_Icc_of_norm_sq hn x y hx hy))
    (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg (n+1)))
  rw [← latitudeThree_signedKernel_sub_pairLevel hn μ β hq01 u hu e he W x y] at hh
  have hi : ({s : ℝ | s < -η}.indicator (fun _ => (1 : ℝ))) (overlap x y)=
      ({z : Vector n × Vector n | overlap z.1 z.2 < -η}.indicator (fun _ => (1 : ℝ))) (x,y) := by
    by_cases hneg : overlap x y < -η <;> simp [hneg]
  rw [hi] at hh
  nlinarith

end
end SlowEquilibration.SphericalModel
