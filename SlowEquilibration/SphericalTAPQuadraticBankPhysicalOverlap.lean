-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticBankOverlapBound
public import SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood

@[expose] public section

/-! The actual mixed certificate selects a latitude band on which the
quadratic-bank replica overlap cost is uniformly finite. -/

namespace SlowEquilibration.SphericalTAPQuadraticBankPhysicalOverlap
noncomputable section
open Filter Set MeasureTheory SphericalModel
open SphericalTAPCertificate
open SphericalTAPCriticalAnalyticNeighborhood
open SphericalQuadraticBankOverlapBound
open scoped Topology
set_option autoImplicit false

/-- The source certificate supplies both the strict quadratic-bank margin
and a common finite bound on the genuine transverse-sphere replica factor,
uniformly over every smaller contact band. -/
theorem source_mixed_quadratic_bank_overlap_bounded
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q) :
    ∃ b₀ ε₂ C : ℝ,
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      0 < ε₂ ∧ ε₂ < 1 ∧ 0 < C ∧
      (∀ b : ℝ, 0 < b → b ≤ b₀ →
        ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
          2*β^2*sourceQuadraticLatitudeVariance μ a ≤ 1-ε₂) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ y : Vector n, ‖y‖^2=(n:ℝ) →
          ∀ b : ℝ, 0 < b → b ≤ b₀ →
            ∀ a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
              (∫ z : Vector n,
                Real.exp (β^2*sourceQuadraticLatitudeVariance μ a*
                  ((n+1:ℕ):ℝ)*(overlap y z)^2) ∂sphereLaw n) ≤ C := by
  obtain ⟨b₀,ε₂,hb₀,hb₀q,hε₂,hε₂1,hband,hmargin⟩ :=
    quadratic_fixed_band_margin μ h
  have hc : ∀ a ∈ Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀),
      0 ≤ β^2*sourceQuadraticLatitudeVariance μ a ∧
        2*(β^2*sourceQuadraticLatitudeVariance μ a) ≤ 1-ε₂ := by
    intro a ha
    have ha0 : 0 < a := (hband ha).1
    have hxi : 0 < μ.xi2 (a^2) := μ.xi2_pos (sq_pos_of_pos ha0)
    constructor
    · unfold sourceQuadraticLatitudeVariance
      positivity
    · simpa only [mul_assoc] using hmargin b₀ hb₀ le_rfl a ha
  obtain ⟨C,hC,hbound⟩ := quadratic_bank_overlap_factor_eventually_bounded
    hε₂ hε₂1.le (Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀))
      (fun a => β^2*sourceQuadraticLatitudeVariance μ a) hc
  refine ⟨b₀,ε₂,C,hb₀,hb₀q,hε₂,hε₂1,hC,hmargin,?_⟩
  filter_upwards [hbound] with n hn
  intro y hy b hb hbb a ha
  have ha' : a ∈ Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀) :=
    ⟨by linarith [ha.1,hbb],by linarith [ha.2,hbb]⟩
  exact hn y hy a ha'

end
end SlowEquilibration.SphericalTAPQuadraticBankPhysicalOverlap
