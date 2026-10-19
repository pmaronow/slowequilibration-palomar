-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereHessian
public import SlowEquilibration.GOEMaximumDeterminant

/-! Strict quadratic negativity of actual operators: Borel measurability,
coordinate invariance, and the genuine spectral criterion. -/
@[expose] public section
namespace SlowEquilibration.NegativeDefiniteOperators
open Set MeasureTheory
open OAI.CriticalSK GOEAsymptotics GOEMaximumDeterminant
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def NegativeDefinite (T : E →L[ℝ] E) : Prop := ∀ v : E, v ≠ 0 → inner ℝ v (T v) < 0

omit [FiniteDimensional ℝ E] in
lemma negativeDefinite_iff_sphere (T : E →L[ℝ] E) :
    NegativeDefinite T ↔ ∀ u : ↥(Metric.sphere (0:E) 1), inner ℝ (u:E) (T u) < 0 := by
  constructor
  · intro h u
    apply h
    have hu : ‖(u:E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  · intro h v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hh := h ⟨‖v‖⁻¹ • v, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩
    change inner ℝ (‖v‖⁻¹ • v) (T (‖v‖⁻¹ • v)) < 0 at hh
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc] at hh
    have hp := mul_pos (inv_pos.mpr hn) (inv_pos.mpr hn)
    nlinarith

lemma isOpen_negativeDefinite : IsOpen {T : E →L[ℝ] E | NegativeDefinite T} := by
  let S := ↥(Metric.sphere (0:E) 1)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0:E) 1)
  have hc : Continuous (fun p : (E →L[ℝ] E) × S => inner ℝ (p.2:E) (p.1 p.2)) :=
    (continuous_subtype_val.comp continuous_snd).inner
      (continuous_fst.clm_apply (continuous_subtype_val.comp continuous_snd))
  have hclosed := isClosedMap_fst_of_compactSpace (X := E →L[ℝ] E) (Y := S)
    {p : (E →L[ℝ] E) × S | 0 ≤ inner ℝ (p.2:E) (p.1 p.2)}
    (isClosed_le (continuous_const (y := (0:ℝ))) hc)
  have he : {T : E →L[ℝ] E | NegativeDefinite T}ᶜ =
      Prod.fst '' {p : (E →L[ℝ] E) × S | 0 ≤ inner ℝ (p.2:E) (p.1 p.2)} := by
    ext T
    simp only [mem_compl_iff, mem_ofPred_eq, negativeDefinite_iff_sphere, not_forall,
      not_lt, mem_image, Prod.exists]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨T,u,hu,rfl⟩
    · rintro ⟨T',u,hu,rfl⟩
      exact ⟨u,hu⟩
  apply isClosed_compl_iff.mp
  rw [he]
  exact hclosed

lemma negativeDefinite_pullback_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F) (T : F →L[ℝ] F) :
    NegativeDefinite (SphereHessian.pullback e T) ↔ NegativeDefinite T := by
  have he (v : E) : inner ℝ v (SphereHessian.pullback e T v) = inner ℝ (e v) (T (e v)) := by
    exact (e : E →L[ℝ] F).adjoint_inner_right v (T (e v))
  constructor
  · intro h v hv
    have hh := h (e.symm v) (by intro h0; apply hv; simpa using congrArg e h0)
    rw [he, e.apply_symm_apply] at hh
    exact hh
  · intro h v hv
    rw [he]
    exact h (e v) (by intro h0; apply hv; exact e.injective (h0.trans (map_zero e).symm))

/-- Strict negativity of a shifted symmetric operator is equivalent to
every genuine eigenvalue lying below the shift. -/
lemma negativeDefinite_shift_iff (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    {m : ℕ} (hm : Module.finrank ℝ E = m) (k : ℝ) :
    NegativeDefinite (T - k • ContinuousLinearMap.id ℝ E) ↔ ∀ i : Fin m, hT.eigenvalues hm i < k := by
  let B := hT.eigenvectorBasis hm
  constructor
  · intro h i
    have hh := h (B i) (B.orthonormal.ne_zero i)
    have hv : ‖B i‖ = 1 := B.norm_eq_one i
    have he : T (B i) = hT.eigenvalues hm i • B i := hT.apply_eigenvectorBasis hm i
    change inner ℝ (B i) (T (B i) - k • B i) < 0 at hh
    rw [he, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hv] at hh
    norm_num at hh
    linarith
  · intro h v hv
    have hv' : B.repr v ≠ 0 := by intro hh; apply hv; exact B.repr.injective (hh.trans (map_zero _).symm)
    have hi : ∃ i : Fin m, B.repr v i ≠ 0 := by
      by_contra! hh
      apply hv'
      ext i
      exact hh i
    obtain ⟨i,hi⟩ := hi
    change inner ℝ v (T v - k • v) < 0
    have hq : basisQuadratic B (hT.eigenvalues hm) v = inner ℝ v (T v) :=
      eigenbasisQuadratic_eq hT hm v
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      ← hq, ← basis_sum_squares B v]
    change (∑ j, hT.eigenvalues hm j * (B.repr v j)^2) - k*(∑ j, (B.repr v j)^2) < 0
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_neg'
    · intro j _
      nlinarith [sq_nonneg (B.repr v j), h j]
    · exact ⟨i, Finset.mem_univ i, by nlinarith [sq_pos_of_ne_zero hi, h i]⟩

end
end SlowEquilibration.NegativeDefiniteOperators
