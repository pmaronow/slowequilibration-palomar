-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureBankSecondMoment
public import SlowEquilibration.SphericalTAPQuadraticBankPhysicalOverlap

@[expose] public section

/-! The certificate's overlap margin also controls the genuine quadratic
latitude bank under the proper-pure value-and-gradient posterior. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter Set SphericalModel SphericalGaussianJet
open SphericalTAPCertificate SphericalTAPQuadraticBankPhysicalOverlap
open ConditionedDeterminantMoments SphericalMarkedWindows
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Uniform second moment of the original-tensor quadratic bank under every
pure Palm energy mark and every latitude in the certificate's contact band. -/
theorem quadraticBankPartition_pure_certificate_uniform_secondMoment
    (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    {β x Q : ℝ} (h : Certificate μ β x Q) :
    ∃ b₀ C : ℝ, 0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
          (energy : ℝ) (b : ℝ), 0 < b → b ≤ b₀ →
          ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            (∫ J, (quadraticBankPartition μ a β u J)^2
              ∂valueConditionedLaw
                (centerCoefficients (mixtureCoefficients μ) Q) u hu energy) ≤
              C*(∫ J, quadraticBankPartition μ a β u J
                ∂valueConditionedLaw
                  (centerCoefficients (mixtureCoefficients μ) Q) u hu energy)^2 := by
  obtain ⟨b₀,ε₂,C,hb₀,hb₀Q,hε₂,hε₂1,hC,hmargin,hbound⟩ :=
    source_mixed_quadratic_bank_overlap_bounded μ h
  refine ⟨b₀,C,hb₀,hb₀Q,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hbound] with d hd
  intro u hu energy b hb hbb a ha
  apply quadraticBankPartition_physicalPurePalm_secondMoment_le_of_overlap
    μ hμ Q a β C u hu energy
  intro y hy
  exact hd y hy b hb hbb a ha

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
