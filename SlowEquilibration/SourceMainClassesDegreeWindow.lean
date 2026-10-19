-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMainClassesLiterature

/-! The explicit degree-support example in manuscript `cor:main-classes`(b).
Every nonzero nonnegative mixture supported in degrees four through eleven
satisfies the strict degree-window inequality, including mixtures of either
parity and pure mixtures. The endpoint retains precisely the five explicit
literature interfaces used by the general main-classes theorem. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMainClassesDegreeWindow

open Set SphericalModel SourceMainClassesLiterature
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24

set_option autoImplicit false

/-- The numerical sufficient condition holds for every pair of extreme
supported degrees in the manuscript's displayed set `{4, …, 11}`. -/
theorem degree_window_four_through_eleven {d P : ℕ}
    (hd : 4 ≤ d) (hdP : d ≤ P) (hP : P ≤ 11) :
    ((d : ℝ) + P - 5) ^ 2 < 6 * ((d : ℝ) - 2) * ((P : ℝ) - 2) := by
  have hd11 : d ≤ 11 := le_trans hdP hP
  interval_cases d <;> interval_cases P <;> norm_num

/-- The `{4, …, 11}` specialization of source `cor:main-classes`(b),
with the literal main theorem and the same-exponent initial-law clause (i).
Only supported degrees are restricted; zero coefficients are allowed. -/
theorem support_four_through_eleven_corollary_b_of_literature
    (μ : FiniteMixture)
    (hsupport : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ} (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : ∀ hβ₀ : 0 ≤ β,
      Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀))
    (h25 : Remark25Contrapositive μ β)
    (h24 : ∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q) :
    MainCondensedAndInitialLiteral μ β := by
  have hmin := Finset.mem_Icc.mp
    (hsupport μ.minDegree (Finset.min'_mem _ _))
  have hmax := Finset.mem_Icc.mp
    (hsupport μ.maxDegree (Finset.max'_mem _ _))
  have horder : μ.minDegree ≤ μ.maxDegree :=
    (μ.degree_bounds (Finset.min'_mem _ _)).2
  exact degree_window_corollary_b_of_literature μ hmin.1
    (degree_window_four_through_eleven hmin.1 horder hmax.2)
    hβ hChen hChenSen h5 h25 h24

end SlowEquilibration.SourceMainClassesDegreeWindow
