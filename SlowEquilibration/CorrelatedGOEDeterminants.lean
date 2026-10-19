-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNormalizedCorrelation
public import SlowEquilibration.GOEPhysicalNormalizedMoments
public import SlowEquilibration.CanonicalGOERealization

/-! Genuine dimension-free factorization of ordinary absolute determinants
of two actual correlated GOE matrices, with each own ordinary mean. -/
@[expose] public section
namespace SlowEquilibration.CorrelatedGOEDeterminants
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open GaussianMaximalCorrelation GOEAsymptotics GOEDeterminantMoments GOEScaling GOERawMoments
open GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

abbrev Coordinates (n : ℕ) := (CanonicalGOERealization.CoefficientIndex (n+1)) → ℝ

def physicalMatrix (n j : ℕ) (b : ℝ) (z : Coordinates n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  scaleFactor n (n+1+j) b • realization n (CanonicalGOERealization.flattenEquiv (n+1) (WithLp.toLp 2 z))

def normalizedDeterminant (n j : ℕ) (b k : ℝ) (z : Coordinates n) : ℝ :=
  matrixAbsoluteDet n k (physicalMatrix n j b z)/physicalMean n (n+1+j) b k

lemma physicalMatrix_measurable (n j : ℕ) (b : ℝ) : Measurable (physicalMatrix n j b) := by
  exact (measurable_const : Measurable (fun _ : Coordinates n => (scaleFactor n (n+1+j) b : ℝ))).smul ((realization_measurable n).comp
    ((CanonicalGOERealization.flattenEquiv (n+1)).continuous.measurable.comp (WithLp.measurable_toLp 2 _)))

lemma normalizedDeterminant_measurable (n j : ℕ) (b k : ℝ) : Measurable (normalizedDeterminant n j b k) := by
  exact ((matrixAbsoluteDet_measurable n k).comp (physicalMatrix_measurable n j b)).div_const _

/-- Literal Gaussian-coordinate pushforward to the actual variance-b/N GOE. -/
theorem physicalMatrix_law (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (γpi (CanonicalGOERealization.CoefficientIndex (n+1))).map (physicalMatrix n j b)=
      SphericalGaussianJet.goeLaw (n+1) (n+1+j) b := by
  let e:=CanonicalGOERealization.flattenEquiv (n+1)
  have hflat : (γpi (CanonicalGOERealization.CoefficientIndex (n+1))).map (WithLp.toLp 2)=
      stdGaussian (EuclideanSpace ℝ (CanonicalGOERealization.CoefficientIndex (n+1))) := map_pi_eq_stdGaussian
  have hmap : (γpi (CanonicalGOERealization.CoefficientIndex (n+1))).map (fun z => e (WithLp.toLp 2 z))=
      stdGaussian (GaussianMatrix (n+1)) := by
    rw [← stdGaussian_map e,← hflat,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h:=congrArg (fun μ => μ.map (fun A : GaussianMatrix (n+1) =>
    scaleFactor n (n+1+j) b • realization n A)) hmap
  have hreal : Measurable (fun A : GaussianMatrix (n+1) => scaleFactor n (n+1+j) b • realization n A) :=
    (measurable_const : Measurable (fun _ : GaussianMatrix (n+1) => (scaleFactor n (n+1+j) b : ℝ))).smul (realization_measurable n)
  rw [Measure.map_map hreal (by fun_prop),scaled_realization_law n (by omega) hb] at h
  exact h

lemma normalizedDeterminant_mean (n j : ℕ) {b k : ℝ}
    (_hD : Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n+1) (n+1+j) b))
    (hb : 0 ≤ b) (hmean : 0 < physicalMean n (n+1+j) b k) :
    (∫ z,normalizedDeterminant n j b k z ∂γpi (CanonicalGOERealization.CoefficientIndex (n+1)))=1 := by
  unfold normalizedDeterminant
  rw [← integral_map (physicalMatrix_measurable n j b).aemeasurable
    ((matrixAbsoluteDet_measurable n k).div_const _).aestronglyMeasurable,physicalMatrix_law n j hb,integral_div]
  exact div_self hmean.ne'

/-- Uniform genuine second moments for the coordinate realizations, with
actual expectation one and actual L² integrability. -/
theorem normalizedDeterminant_L2_uniform (j : ℕ) {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ C : ℝ,0 < C ∧ ∀ n : ℕ,∀ k : ℝ,2*Real.sqrt b+g ≤ k → k ≤ Z →
      MemLp (normalizedDeterminant n j b k) 2 (γpi (CanonicalGOERealization.CoefficientIndex (n+1))) ∧
        (∫ z,normalizedDeterminant n j b k z ∂γpi (CanonicalGOERealization.CoefficientIndex (n+1)))=1 ∧
        (∫ z,normalizedDeterminant n j b k z^2 ∂γpi (CanonicalGOERealization.CoefficientIndex (n+1))) ≤ C := by
  obtain ⟨C,hC,hall⟩:=normalized_physical_moments j (Z:=Z) hb hg (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨C,hC,?_⟩
  intro n k hk hZ
  have hactual:=hall n k hk hZ
  have hmeas:=normalizedDeterminant_measurable n j b k
  have hsq : Integrable (fun z => normalizedDeterminant n j b k z^2) (γpi (CanonicalGOERealization.CoefficientIndex (n+1))) := by
    have hh : Integrable (fun W => (matrixAbsoluteDet n k W/physicalMean n (n+1+j) b k)^2)
        (SphericalGaussianJet.goeLaw (n+1) (n+1+j) b) := by simpa only [Real.rpow_two] using hactual.2.2.1
    rw [← physicalMatrix_law n j hb.le] at hh
    exact (integrable_map_measure (((matrixAbsoluteDet_measurable n k).div_const _).pow_const 2).aestronglyMeasurable
      (physicalMatrix_measurable n j b).aemeasurable).mp hh
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hsq,
    normalizedDeterminant_mean n j hactual.1 hb.le hactual.2.1,?_⟩
  unfold normalizedDeterminant
  rw [← integral_map (physicalMatrix_measurable n j b).aemeasurable
    (((matrixAbsoluteDet_measurable n k).div_const _).pow_const 2).aestronglyMeasurable,
    physicalMatrix_law n j hb.le]
  simpa only [Real.rpow_two] using hactual.2.2.2

/-- Actual ordinary absolute GOE determinants factorize with O(|ρ|) error,
uniformly in dimension and compact outside-edge shifts. No factorization
or Gaussian-maximal-correlation theorem is supplied as an input. -/
theorem normalized_correlated_goe_determinants (j : ℕ) {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ C : ℝ,0 < C ∧ ∀ n : ℕ,∀ k1 k2 : ℝ,
      2*Real.sqrt b+g ≤ k1 → k1 ≤ Z → 2*Real.sqrt b+g ≤ k2 → k2 ≤ Z →
      ∀ ρ s : ℝ,ρ^2+s^2=1 → |ρ| ≤ 1 →
      Integrable (fun z : Coordinates n×Coordinates n =>
        normalizedDeterminant n j b k1 z.1*normalizedDeterminant n j b k2 (ρ • z.1+s • z.2))
          ((γpi (CanonicalGOERealization.CoefficientIndex (n+1))).prod (γpi (CanonicalGOERealization.CoefficientIndex (n+1)))) ∧
      |(∫ z : Coordinates n×Coordinates n,
        normalizedDeterminant n j b k1 z.1*normalizedDeterminant n j b k2 (ρ • z.1+s • z.2)
          ∂(γpi (CanonicalGOERealization.CoefficientIndex (n+1))).prod (γpi (CanonicalGOERealization.CoefficientIndex (n+1))))-1| ≤ C * |ρ| := by
  obtain ⟨C,hC,hall⟩:=normalizedDeterminant_L2_uniform j (Z:=Z) hb hg
  refine ⟨C,hC,?_⟩
  intro n k1 k2 hk1 hZ1 hk2 hZ2 ρ s hrot hρ
  have h1:=hall n k1 hk1 hZ1
  have h2:=hall n k2 hk2 hZ2
  exact normalized_coupled_factorization ρ s hrot hρ (normalizedDeterminant_measurable n j b k1)
    (normalizedDeterminant_measurable n j b k2) h1.1 h2.1 h1.2.1 h2.2.1 hC.le h1.2.2 h2.2.2

end
end SlowEquilibration.CorrelatedGOEDeterminants
