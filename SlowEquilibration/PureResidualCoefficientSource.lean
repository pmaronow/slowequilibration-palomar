-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureResidualCoefficient
public import SlowEquilibration.PureRootUniqueness
public import SlowEquilibration.FiniteMixtureTaylorResidual

@[expose] public section
/-! The full source Lemma 5.22 for the canonical pure spherical model.
The overlap is selected by the original two-atom minimizer and its unique
positive-branch root. The coefficient is the literal Taylor residual of the
original covariance, with its derivative and the printed numerical margin. -/
namespace SlowEquilibration.PureStationarity
noncomputable section
open Set PureScalarStatic
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- At the exact latitude `sqrt Q`, the pure coefficient is the manuscript's
residual covariance at overlap one. -/
theorem pureResidualCoefficient_sqrt_eq_taylorResidual
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ) {Q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    pureResidualCoefficient p β (Real.sqrt Q) =
      β ^ 2 * (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1 := by
  dsimp only
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  have hξ := μ.taylorResidual_xi hQ.1 (sub_pos.mpr hQ.2) 1
  have hvalue : μ.xi 1 = 1 := by
    simp [μ, FiniteMixture.pure_xi]
  have hcenter : μ.xi Q = Q ^ p := by
    simp [μ, FiniteMixture.pure_xi]
  have hderiv : μ.xi1 Q = (p : ℝ) * Q ^ (p-1) := by
    exact pure_xi1 p hp Q
  rw [show Q + (1-Q)*(1:ℝ)=1 by ring, hvalue, hcenter, hderiv] at hξ
  rw [pureResidualCoefficient, Real.sq_sqrt hQ.1.le, pureResidualAtOne]
  rw [hξ]
  ring

/-- The displayed derivative in Lemma 5.22, with its sign on every source
latitude, follows from the actual polynomial coefficient. -/
theorem pureResidualCoefficient_source_derivative
    (p : ℕ) (hp : 4 ≤ p) (β : ℝ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    deriv (pureResidualCoefficient p β) a =
        -2*β^2*(p : ℝ)*((p : ℝ)-1)*a^(2*p-3)*(1-a^2) ∧
      deriv (pureResidualCoefficient p β) a ≤ 0 := by
  have hd := (pureResidualCoefficient_hasDerivAt p (by omega : 2 ≤ p) β a).deriv
  refine ⟨hd, ?_⟩
  rw [hd]
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : 0 ≤ a^(2*p-3) := pow_nonneg ha.1 _
  have hs : 0 ≤ 1-a^2 := by nlinarith [ha.1, ha.2]
  have hnonneg : 0 ≤ 2*β^2*(p : ℝ)*((p : ℝ)-1)*a^(2*p-3)*(1-a^2) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity : 0 ≤ 2*β^2) (by positivity : 0 ≤ (p : ℝ)))
          (by linarith : 0 ≤ (p : ℝ)-1)) hpow) hs
  linarith

/-- Manuscript Lemma 5.22 in its canonical pure-model specialization.
The unique root clause identifies `Q` with the overlap selected in the
preceding pure-model proposition, rather than choosing an arbitrary root. -/
theorem source_pure_residualCoefficient (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ∃ Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1,
        ∃ hQ0 : Q ∈ Ioo (0 : ℝ) 1,
        (CSParisiMeasure.canonicalMinimizer
          (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law =
          CrisantiSommers.twoAtom x Q ∧
        (∀ R ∈ Ioo (staticOverlap (zParameter p (by omega))) 1,
          β^2*(p : ℝ)*(1+zParameter p (by omega))*R^(p-2)*(1-R)^2 = 1 → R = Q) ∧
        (pureResidualCoefficient p β (Real.sqrt Q) =
          β^2*((FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)).taylorResidual
            hQ0.1 (sub_pos.mpr hQ0.2)).xi 1) ∧
        pureResidualCoefficient p β (Real.sqrt Q) < (159/320 : ℝ) ∧
        (159/320 : ℝ) < 1/2 ∧
        ∀ a ∈ Icc (0 : ℝ) 1,
          pureResidualCoefficient p β a =
            β^2*(1-a^(2*p)-(p : ℝ)*a^(2*p-2)*(1-a^2)) ∧
          (deriv (pureResidualCoefficient p β) a =
              -2*β^2*(p : ℝ)*((p : ℝ)-1)*a^(2*p-3)*(1-a^2) ∧
            deriv (pureResidualCoefficient p β) a ≤ 0) := by
  obtain ⟨x, hx, Q, hQ, hlaw, hxformula, hroot, hcurv, hpositive⟩ :=
    canonical_pure_parameters p (by omega : 3 ≤ p) hβ
  have hQ0 : Q ∈ Ioo (0 : ℝ) 1 :=
    ⟨(staticOverlap_mem_Ioo (zParameter_spec p (by omega)).1).1.trans hQ.1, hQ.2⟩
  have hβne : β ≠ 0 := by
    intro heq
    rw [heq] at hroot
    norm_num at hroot
  refine ⟨x, hx, Q, hQ, hQ0, hlaw, ?_, ?_, ?_, by norm_num, ?_⟩
  · intro R hR hRroot
    exact pure_plateau_root_unique p hp hR hQ hβne hRroot hroot
  · exact pureResidualCoefficient_sqrt_eq_taylorResidual p (by omega) β hQ0
  · have hb := pureResidualAtOne_bound_of_root p hp hQ hroot
    change β^2*pureResidualAtOne p ((Real.sqrt Q)^2) < (159/320 : ℝ)
    rw [Real.sq_sqrt hQ0.1.le]
    exact hb
  · intro a ha
    exact ⟨pureResidualCoefficient_eq p (by omega) β a,
      pureResidualCoefficient_source_derivative p hp β a ha⟩

end
end SlowEquilibration.PureStationarity
