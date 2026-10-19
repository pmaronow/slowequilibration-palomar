-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureSourceQuadraticBound
public import SlowEquilibration.SphericalQuadraticLatitudeJetPureResidualMGF

@[expose] public section

/-! Complete proper-pure source quadratic-correlation section, for the
literal original tensor field, actual value/gradient Palm posterior,
intrinsic determinant, and physical transverse latitude sphere. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter Set SphericalModel ConditionedDeterminantMoments
open SphericalTAPCertificate SphericalTAPCriticalAnalyticNeighborhood
open SphericalTAPCriticalPureLatitudeVariance GOEPhysicalPotential
open scoped Topology
set_option autoImplicit false

theorem source_mb_quadratic_physicalPurePalm
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) (e : ℝ),
          2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*e →
          ∀ (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            Integrable (fun J => intrinsicDet μ Q u J *
              partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
                (field (mixtureCoefficients μ) J))
              (pureLaw p hp alpha halpha Q u hu e) ∧
            (∫ J, intrinsicDet μ Q u J *
              partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
                (field (mixtureCoefficients μ) J)
              ∂pureLaw p hp alpha halpha Q u hu e) ≤
                C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
                  Real.exp (((d+2:ℕ):ℝ)*
                    (β*e*(a/Real.sqrt Q)^p+
                      β^2/2*sourcePureLatitudeVariance p alpha a)) := by
  have hμ : 3 ≤ (FiniteMixture.pure p hp alpha halpha).minDegree := by
    have hh : 4 ≤ (FiniteMixture.pure p hp alpha halpha).minDegree := h.min_degree
    omega
  apply source_mb_quadratic_physicalPurePalm_of_residualMGF
    p hp alpha halpha h hg
  intro d u hu e a ha ω hω hωn
  exact nonquadraticLatitudeField_physicalPurePalm_exp_integral
    p hp alpha halpha hμ h.overlap_range.1 a β ha u ω hu hω hωn e

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
