-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetBounds
public import SlowEquilibration.GaussianNormConcentration

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureTensorJetConcentration
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel PureTensorJetFeatures PureTensorJetBounds
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def euclideanEnvelope (N p j : ℕ) (g : EuclideanSpace ℝ (TensorIndex N p)) : ℝ :=
  pureJetEnvelope N p j (WithLp.ofLp g)

/-- The actual unnormalized operator-jet envelope is `p^j`-Lipschitz in all
tensor coefficients, independently of the number of coefficients. -/
theorem unitEnvelope_lipschitz {N p j : ℕ} (hN : 0 < N) :
    LipschitzWith ((p : ℝ)^j).toNNReal
      (fun g : EuclideanSpace ℝ (TensorIndex N p) => unitJetEnvelope N p j (WithLp.ofLp g)) := by
  letI : NeZero N := ⟨hN.ne'⟩
  apply GaussianCompactMaximum.field_supremum_lipschitz
    (fun v : Bool × UnitBlocks N j => innerSL ℝ (signedFeature (unitInsertion N p j) v))
  intro v
  have hn := insertionFeature_norm_le (p := p) (fun k => (v.2 k).val) (fun k => unit_norm (v.2 k))
  simpa [signedFeature,norm_smul,norm_sign,unitInsertion] using hn

/-- The physical coefficient-to-jet Lipschitz scale. -/
theorem physical_lipschitz_normalization {N p j : ℕ} (hN : 0 < N)
    (hp : 1 ≤ p) (hj : j ≤ p) :
    normalization N p * Real.sqrt N ^ (p-j) = (N : ℝ) ^ ((1-(j : ℝ))/2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [normalization,Real.sqrt_eq_rpow,← Real.rpow_natCast,
    ← Real.rpow_mul hNr.le,← Real.rpow_add hNr]
  congr 1
  rw [Nat.cast_sub hj,Nat.cast_sub hp]
  push_cast
  ring

theorem euclideanEnvelope_lipschitz {N p j : ℕ} (hN : 0 < N)
    (hp : 1 ≤ p) (hj : j ≤ p) :
    LipschitzWith (((N : ℝ)^((1-(j : ℝ))/2))*(p : ℝ)^j).toNNReal
      (euclideanEnvelope N p j) := by
  apply LipschitzWith.of_dist_le_mul
  intro g z
  have he : euclideanEnvelope N p j g - euclideanEnvelope N p j z =
      ((N : ℝ)^((1-(j : ℝ))/2)) *
        (unitJetEnvelope N p j (WithLp.ofLp g)-unitJetEnvelope N p j (WithLp.ofLp z)) := by
    simp only [euclideanEnvelope,pureJetEnvelope,← mul_sub,physical_lipschitz_normalization hN hp hj]
  rw [Real.dist_eq,he,abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
    Real.coe_toNNReal _ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by positivity))]
  have hh := (unitEnvelope_lipschitz (p := p) (j := j) hN).dist_le_mul g z
  rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity)] at hh
  calc
    _ ≤ ((N : ℝ)^((1-(j : ℝ))/2)) * ((p : ℝ)^j * dist g z) := by gcongr
    _ = _ := by ring

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev Coordinate (N : ℕ) (d : σ → ℕ) := (i : σ) × TensorIndex N (d i)

def blockProjection {N : ℕ} (d : σ → ℕ) (i : σ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : EuclideanSpace ℝ (TensorIndex N (d i)) :=
  WithLp.toLp 2 (fun I => g ⟨i,I⟩)

def weightedEnvelope {N : ℕ} (d : σ → ℕ) (w : σ → ℝ) (j : ℕ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : ℝ :=
  ∑ i,w i * euclideanEnvelope N (d i) j (blockProjection d i g)

theorem projection_norm_sum {N : ℕ} (d : σ → ℕ)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    (∑ i,‖blockProjection d i g‖^2) = ‖g‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,blockProjection,Fintype.sum_sigma]

theorem blockProjection_sub {N : ℕ} (d : σ → ℕ) (i : σ)
    (g z : EuclideanSpace ℝ (Coordinate N d)) :
    blockProjection d i (g-z) = blockProjection d i g - blockProjection d i z := by ext I; rfl

/-- Independent coefficient blocks combine by the square root of the sum of
squared Lipschitz constants, preserving the exponential dimension scale. -/
theorem weightedEnvelope_lipschitz {N j : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (w : σ → ℝ) (hw : ∀ i,0 ≤ w i)
    (hd : ∀ i,1 ≤ d i) (hj : ∀ i,j ≤ d i) :
    LipschitzWith
      ((N : ℝ)^((1-(j : ℝ))/2) * Real.sqrt (∑ i,(w i * (d i : ℝ)^j)^2)).toNNReal
      (weightedEnvelope (N := N) d w j) := by
  let D : ℝ := (N : ℝ)^((1-(j : ℝ))/2)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg N) _
  apply LipschitzWith.of_dist_le_mul
  intro g z
  rw [Real.coe_toNNReal _ (mul_nonneg hD (Real.sqrt_nonneg _)),Real.dist_eq]
  have hb (i : σ) :
      |w i * euclideanEnvelope N (d i) j (blockProjection d i g) -
        w i * euclideanEnvelope N (d i) j (blockProjection d i z)| ≤
        D * (w i * (d i : ℝ)^j) * ‖blockProjection d i (g-z)‖ := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (hw i)]
    have hi := (euclideanEnvelope_lipschitz hN (hd i) (hj i)).dist_le_mul
      (blockProjection d i g) (blockProjection d i z)
    rw [Real.dist_eq,Real.coe_toNNReal _ (mul_nonneg hD (by positivity)),
      dist_eq_norm,← blockProjection_sub] at hi
    exact (mul_le_mul_of_nonneg_left hi (hw i)).trans_eq (by dsimp [D]; ring)
  have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => w i*(d i : ℝ)^j) (fun i => ‖blockProjection d i (g-z)‖)
  rw [projection_norm_sum,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] at hs
  calc
    _ ≤ ∑ i,|w i * euclideanEnvelope N (d i) j (blockProjection d i g) -
        w i * euclideanEnvelope N (d i) j (blockProjection d i z)| := by
      rw [weightedEnvelope,weightedEnvelope,← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,D * (w i * (d i : ℝ)^j) * ‖blockProjection d i (g-z)‖ :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = D * ∑ i,(w i * (d i : ℝ)^j) * ‖blockProjection d i (g-z)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ D * (Real.sqrt (∑ i,(w i*(d i : ℝ)^j)^2) * ‖g-z‖) :=
      mul_le_mul_of_nonneg_left hs hD
    _ = _ := by rw [dist_eq_norm]; ring

/-- Genuine finite Gaussian concentration of the actual uniform jet envelope. -/
theorem weightedEnvelope_centered_upper_tail {N j : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (w : σ → ℝ) (hw : ∀ i,0 ≤ w i)
    (hd : ∀ i,1 ≤ d i) (hj : ∀ i,j ≤ d i) {s : ℝ} (hs : 0 ≤ s) :
    (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g | (∫ z,weightedEnvelope d w j z ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+s ≤
        weightedEnvelope d w j g} ≤
      Real.exp (-s^2/(2*((N : ℝ)^((1-(j : ℝ))/2) *
        Real.sqrt (∑ i,(w i*(d i : ℝ)^j)^2))^2)) :=
  GaussianNormConcentration.centered_lipschitz_upper_tail _
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.sqrt_nonneg _))
    (weightedEnvelope_lipschitz hN d w hw hd hj) hs

end SlowEquilibration.PureTensorJetConcentration
