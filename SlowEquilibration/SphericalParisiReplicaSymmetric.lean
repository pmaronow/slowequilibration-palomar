-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralRSPressure
public import SlowEquilibration.CSParisiMeasure

@[expose] public section

/-!
# The physical spherical Parisi formula throughout the closed RS sector

This states the genuine equality of the thermodynamic tensor-model pressure
and the actual unique ordinary CS variational minimum, throughout
`0 ≤ beta ≤ beta_s`, for every finite mixture, including quadratic and odd
terms. The physical lower bound is the existing Gaussian HS truncation proof;
no thermodynamic or moment hypothesis replaces that lower bound.

The all-temperature formula, and covariance polynomials with a linear term,
are distinct open obligations of manuscript Theorem 3.14.
-/

namespace SlowEquilibration.SphericalModel

open Filter MeasureTheory
open scoped Topology

/-- The closed replica-symmetric sector of source Theorem 3.14, for the
literal tensor model and its actual existing variational minimizer. -/
theorem general_parisi_formula_le_static (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) :
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop
      (𝓝 (CSParisiMeasure.variationalValue μ β)) := by
  rw [(CSParisiMeasure.variationalValue_eq_annealed_iff μ hβ).mpr hβs]
  exact general_quenchedPressure_tendsto_annealed_le_static μ hβ hβs

end SlowEquilibration.SphericalModel
