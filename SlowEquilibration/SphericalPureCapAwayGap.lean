-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapSourceScalars

@[expose] public section

/-! Fixed exponential separation of the pure cap exponent from its saddle. -/

namespace SlowEquilibration.SphericalPureCapAwayGap
noncomputable section
open Set
set_option autoImplicit false

/-- Strict monotonicity on both sides of the saddle supplies one fixed
exponent gap outside any smaller contact window. The right side extends all
the way to the pole, where the latitude Jacobian needs separate handling. -/
theorem cap_exponent_gap_away_from_contact
    (φ : ℝ → ℝ) {a l q r : ℝ}
    (hal : a ≤ l) (hlq : l < q) (hqr : q < r) (hr1 : r < 1)
    (hleft : StrictMonoOn φ (Icc a q))
    (hright : StrictAntiOn φ (Ico q 1)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Ico a 1, (t ≤ l ∨ r ≤ t) → φ t ≤ φ q-δ := by
  have hlgap : 0 < φ q-φ l := by
    have hlt := hleft ⟨hal,hlq.le⟩ ⟨le_trans hal hlq.le,le_refl q⟩ hlq
    linarith
  have hrgap : 0 < φ q-φ r := by
    have hlt := hright ⟨le_refl q,lt_trans hqr hr1⟩ ⟨hqr.le,hr1⟩ hqr
    linarith
  let δ := min (φ q-φ l) (φ q-φ r)
  have hδ : 0 < δ := lt_min hlgap hrgap
  refine ⟨δ,hδ,?_⟩
  intro t ht haway
  rcases haway with htl|hrt
  · have htle : φ t ≤ φ l := by
      rcases eq_or_lt_of_le htl with heq|hlt
      · simp [heq]
      · exact (hleft ⟨ht.1,(lt_trans hlt hlq).le⟩ ⟨hal,hlq.le⟩ hlt).le
    have hgap := min_le_left (φ q-φ l) (φ q-φ r)
    dsimp only [δ]
    linarith
  · have hrle : φ t ≤ φ r := by
      rcases eq_or_lt_of_le hrt with heq|hlt
      · simp [heq.symm]
      · exact (hright ⟨hqr.le,hr1⟩ ⟨(le_trans hqr.le hrt),ht.2⟩ hlt).le
    have hgap := min_le_right (φ q-φ l) (φ q-φ r)
    dsimp only [δ]
    linarith

end
end SlowEquilibration.SphericalPureCapAwayGap
