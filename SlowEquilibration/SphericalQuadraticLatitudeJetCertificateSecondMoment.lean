-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetBankSecondMoment

@[expose] public section

/-! The source certificate's strict quadratic-bank margin supplies the
uniform replica factor. Consequently the literal original-tensor angular
bank has the claimed normalized second-moment bound under every mixed Palm
mark, with one constant and one dimension cutoff throughout a fixed band. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter Set SphericalModel
open SphericalTAPCertificate SphericalTAPQuadraticBankPhysicalOverlap
open ConditionedDeterminantMoments
open scoped Topology
set_option autoImplicit false

/-- The full quadratic-bank second-moment part of source `mb-quadratic`,
with no posterior-bank-law, Fubini, or overlap hypothesis. -/
theorem quadraticBankPartition_certificate_uniform_secondMoment
    (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    {β x Q : ℝ} (h : Certificate μ β x Q) :
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
          (mark : EuclideanSpace ℝ (Fin 2))
          (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            (∫ J, (quadraticBankPartition μ a β u J)^2
              ∂mixedLaw μ Q u hu mark) ≤
              C*(∫ J, quadraticBankPartition μ a β u J
                ∂mixedLaw μ Q u hu mark)^2 := by
  obtain ⟨b₀,ε₂,C,hb₀,hb₀Q,hε₂,hε₂1,hC,hmargin,hbound⟩ :=
    source_mixed_quadratic_bank_overlap_bounded μ h
  refine ⟨b₀,C,hb₀,hb₀Q,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hbound] with d hd
  intro u hu mark b hb hbb a ha
  apply quadraticBankPartition_physicalMixedPalm_secondMoment_le_of_overlap
    μ hμ Q a β C u hu mark
  intro y hy
  exact hd y hy b hb hbb a ha

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
