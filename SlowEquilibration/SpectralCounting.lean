-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Weighted spectral counting

This file proves the coefficient-counting step of Lemma `lem:sp-frame`
("Counting with nonnegative trial functions") in
`Slow_equilibration_hexagon_2026-10-12/source-single-file/slow_equilibration.tex`,
equations `eq:sp-frame-bj` and the subsequent spectral mass argument.

The finite theorem takes nonnegative coefficients `b j`, a nonnegative spectrum
`eigenvalue j`, and an upper frame bound `M` as explicit input. Thus it does **not**
construct the spherical Langevin generator, its eigenbasis, trial functions,
Dirichlet form, or the integrals defining the coefficients. Establishing those
objects and the identities by Parseval and Tonelli remains a separate analytic
task. The theorem itself is a kernel-checked weighted counting inequality.
-/

namespace SlowEquilibration

open scoped BigOperators

/-- Cauchy--Schwarz for a finite nonnegative weighted measure, with no
restriction on the signs of the observable. This is the finite counterpart
of the Cauchy--Schwarz step for the measure `f_u dπ` in `eq:sp-frame-bj`. -/
theorem finite_weighted_cauchy {ι : Type*} (s : Finset ι) (w φ : ι → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x * φ x) ^ 2 ≤
      (∑ x ∈ s, w x) * (∑ x ∈ s, w x * (φ x) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
    (fun x hx => mul_nonneg (hw x hx) (sq_nonneg (φ x)))
  intro x _hx
  exact le_of_eq (by ring)

/-- The upper frame bound `b_j ≤ R*C` in manuscript `eq:sp-frame-bj`, for
finite trial and state spaces with actual nonnegative measure weights.

The squared inner products are computed as weighted finite sums. The row
bound controls the mass of each nonnegative trial function, the column
bound controls coverage of each state, and `hnorm` normalizes the eigenvector.
This proves the finite analogue of the manuscript's Cauchy--Schwarz and
Tonelli argument; it does not claim the measure-theoretic infinite version. -/
theorem finite_nonnegative_frame_bound {U X : Type*}
    (us : Finset U) (xs : Finset X) (μ : U → ℝ) (π : X → ℝ)
    (f : U → X → ℝ) (φ : X → ℝ) (R C : ℝ)
    (hμ : ∀ u ∈ us, 0 ≤ μ u) (hπ : ∀ x ∈ xs, 0 ≤ π x)
    (hf : ∀ u ∈ us, ∀ x ∈ xs, 0 ≤ f u x) (hR : 0 ≤ R)
    (hrow : ∀ u ∈ us, (∑ x ∈ xs, π x * f u x) ≤ R)
    (hcol : ∀ x ∈ xs, (∑ u ∈ us, μ u * f u x) ≤ C)
    (hnorm : (∑ x ∈ xs, π x * (φ x) ^ 2) = 1) :
    (∑ u ∈ us, μ u * (∑ x ∈ xs, π x * f u x * φ x) ^ 2) ≤ R * C := by
  classical
  have hlocal : ∀ u ∈ us,
      (∑ x ∈ xs, π x * f u x * φ x) ^ 2 ≤
        R * (∑ x ∈ xs, π x * f u x * (φ x) ^ 2) := by
    intro u hu
    have hw : ∀ x ∈ xs, 0 ≤ π x * f u x :=
      fun x hx => mul_nonneg (hπ x hx) (hf u hu x hx)
    have hnormu : 0 ≤ (∑ x ∈ xs, π x * f u x * (φ x) ^ 2) :=
      Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (sq_nonneg (φ x)))
    exact (finite_weighted_cauchy xs (fun x => π x * f u x) φ hw).trans
      (mul_le_mul_of_nonneg_right (hrow u hu) hnormu)
  have hfirst : (∑ u ∈ us, μ u * (∑ x ∈ xs, π x * f u x * φ x) ^ 2) ≤
      ∑ u ∈ us, μ u * (R * (∑ x ∈ xs, π x * f u x * (φ x) ^ 2)) :=
    Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hlocal u hu) (hμ u hu))
  have hswap : (∑ u ∈ us, μ u * (R * (∑ x ∈ xs, π x * f u x * (φ x) ^ 2))) =
      R * (∑ x ∈ xs, (π x * (φ x) ^ 2) * (∑ u ∈ us, μ u * f u x)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _hx
    apply Finset.sum_congr rfl
    intro u _hu
    ring
  have hsecond : (∑ x ∈ xs, (π x * (φ x) ^ 2) * (∑ u ∈ us, μ u * f u x)) ≤
      C * (∑ x ∈ xs, π x * (φ x) ^ 2) := by
    calc
      _ ≤ ∑ x ∈ xs, (π x * (φ x) ^ 2) * C := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hcol x hx)
          (mul_nonneg (hπ x hx) (sq_nonneg (φ x)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  calc
    _ ≤ _ := hfirst
    _ = _ := hswap
    _ ≤ R * (C * (∑ x ∈ xs, π x * (φ x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsecond hR
    _ = R * C := by rw [hnorm]; ring

/-- The indices in a finite spectrum whose eigenvalue is at most the cutoff.
The constant eigenfunction, when present in `s`, is included. -/
noncomputable def lowSpectrum {ι : Type*} (s : Finset ι) (eigenvalue : ι → ℝ) (Λ : ℝ) :
    Finset ι := by
  classical
  exact s.filter (fun j => eigenvalue j ≤ Λ)

/-- The elementary spectral mass estimate in the proof of manuscript
Lemma `lem:sp-frame`, for an arbitrary finite coefficient set.

The estimate says that total mass minus the energy divided by the cutoff
is carried by eigenvalues below the cutoff. -/
theorem finite_low_spectral_mass {ι : Type*} (s : Finset ι) (eigenvalue b : ι → ℝ)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hb : ∀ j ∈ s, 0 ≤ b j) (hEigenvalue : ∀ j ∈ s, 0 ≤ eigenvalue j) :
    (∑ j ∈ s, b j) - (∑ j ∈ s, eigenvalue j * b j) / Λ ≤
      ∑ j ∈ lowSpectrum s eigenvalue Λ, b j := by
  classical
  have hpoint : ∀ j ∈ s,
      Λ * b j ≤ eigenvalue j * b j + if eigenvalue j ≤ Λ then Λ * b j else 0 := by
    intro j hj
    split_ifs with hjΛ
    · linarith [mul_nonneg (hEigenvalue j hj) (hb j hj)]
    · simpa using mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hjΛ)) (hb j hj)
  have hsum := Finset.sum_le_sum hpoint
  have hsum' : Λ * (∑ j ∈ s, b j) ≤
      (∑ j ∈ s, eigenvalue j * b j) + Λ * (∑ j ∈ lowSpectrum s eigenvalue Λ, b j) := by
    simpa only [Finset.sum_add_distrib, Finset.mul_sum,
      lowSpectrum, Finset.sum_filter, mul_ite, mul_zero] using hsum
  apply (mul_le_mul_iff_right₀ hΛ).mp
  have hcancel : Λ * ((∑ j ∈ s, b j) - (∑ j ∈ s, eigenvalue j * b j) / Λ) =
      Λ * (∑ j ∈ s, b j) - (∑ j ∈ s, eigenvalue j * b j) := by
    field_simp [ne_of_gt hΛ]
  rw [hcancel]
  linarith

/-- Finite coefficient version of the final counting step of manuscript
Lemma `lem:sp-frame`.

If `T = ∑ b j`, `∑ eigenvalue j * b j ≤ r * T`, and each coefficient is at most `M`,
then there are at least `(1-r/Λ)*T/M` indices below `Λ`.
This theorem counts only the given finite index set `s`; it does not assert
the manuscript's infinite-dimensional spectral construction. -/
theorem finite_weighted_spectral_count {ι : Type*} (s : Finset ι) (eigenvalue b : ι → ℝ)
    (r Λ M : ℝ) (hb : ∀ j ∈ s, 0 ≤ b j)
    (hEigenvalue : ∀ j ∈ s, 0 ≤ eigenvalue j) (hbound : ∀ j ∈ s, b j ≤ M)
    (hM : 0 < M) (hr : 0 ≤ r) (hrΛ : r < Λ)
    (henergy : (∑ j ∈ s, eigenvalue j * b j) ≤ r * (∑ j ∈ s, b j)) :
    (1 - r / Λ) * (∑ j ∈ s, b j) / M ≤
      ((lowSpectrum s eigenvalue Λ).card : ℝ) := by
  classical
  have hΛ : 0 < Λ := lt_of_le_of_lt hr hrΛ
  have henergy' : (∑ j ∈ s, eigenvalue j * b j) / Λ ≤
      r * (∑ j ∈ s, b j) / Λ := (div_le_div_iff_of_pos_right hΛ).2 henergy
  have hmass : (1 - r / Λ) * (∑ j ∈ s, b j) ≤
      ∑ j ∈ lowSpectrum s eigenvalue Λ, b j := by
    have hlow := finite_low_spectral_mass s eigenvalue b Λ hΛ hb hEigenvalue
    calc
      (1 - r / Λ) * (∑ j ∈ s, b j) =
          (∑ j ∈ s, b j) - r * (∑ j ∈ s, b j) / Λ := by ring
      _ ≤ (∑ j ∈ s, b j) - (∑ j ∈ s, eigenvalue j * b j) / Λ := by linarith
      _ ≤ _ := hlow
  have hupper : (∑ j ∈ lowSpectrum s eigenvalue Λ, b j) ≤
      ((lowSpectrum s eigenvalue Λ).card : ℝ) * M := by
    calc
      (∑ j ∈ lowSpectrum s eigenvalue Λ, b j) ≤ ∑ _j ∈ lowSpectrum s eigenvalue Λ, M := by
        apply Finset.sum_le_sum
        intro j hj
        exact hbound j (Finset.mem_filter.mp hj).1
      _ = _ := by simp
  exact (div_le_iff₀ hM).2 (hmass.trans hupper)

/-- The `M = R*C` form of the finite coefficient counting theorem, matching
the constants in manuscript Lemma `lem:sp-frame`.

Here the frame inequality `b j ≤ R*C` is a hypothesis. In the manuscript it
comes from nonnegative trial functions and the row and column bounds in
`eq:sp-frame-rowcol`; that measure-theoretic derivation is not asserted here. -/
theorem finite_frame_spectral_count {ι : Type*} (s : Finset ι) (eigenvalue b : ι → ℝ)
    (r Λ R C : ℝ) (hb : ∀ j ∈ s, 0 ≤ b j)
    (hEigenvalue : ∀ j ∈ s, 0 ≤ eigenvalue j) (hbound : ∀ j ∈ s, b j ≤ R * C)
    (hR : 0 < R) (hC : 0 < C) (hr : 0 ≤ r) (hrΛ : r < Λ)
    (henergy : (∑ j ∈ s, eigenvalue j * b j) ≤ r * (∑ j ∈ s, b j)) :
    (1 - r / Λ) * (∑ j ∈ s, b j) / (R * C) ≤
      ((lowSpectrum s eigenvalue Λ).card : ℝ) :=
  finite_weighted_spectral_count s eigenvalue b r Λ (R * C) hb hEigenvalue hbound
    (mul_pos hR hC) hr hrΛ henergy

/-- The same spectral mass argument for a summable, possibly infinite spectrum.

The finite set `s` must contain exactly the eigenvalue indices at most `Λ`.
Both coefficient mass and coefficient energy have genuine summability
hypotheses, so the real-valued `tsum` cannot silently denote zero for a
divergent series. This is the series calculation in the proof of manuscript
Lemma `lem:sp-frame`, after Parseval, Tonelli, and the frame bound have been
established. -/
theorem summable_low_spectral_mass {ι : Type*} (s : Finset ι) (eigenvalue b : ι → ℝ)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hcut : ∀ j, j ∈ s ↔ eigenvalue j ≤ Λ)
    (hb : ∀ j, 0 ≤ b j) (hEigenvalue : ∀ j, 0 ≤ eigenvalue j)
    (hsumb : Summable b) (hsumenergy : Summable (fun j => eigenvalue j * b j)) :
    (∑' j, b j) - (∑' j, eigenvalue j * b j) / Λ ≤ ∑ j ∈ s, b j := by
  classical
  let low : ι → ℝ := fun j => if j ∈ s then Λ * b j else 0
  have hlowzero : ∀ j ∉ s, low j = 0 := by
    intro j hj
    simp [low, hj]
  have hsumlow : Summable low := summable_of_ne_finset_zero hlowzero
  have hpoint : ∀ j, Λ * b j ≤ eigenvalue j * b j + low j := by
    intro j
    by_cases hj : j ∈ s
    · simp only [low, ite_eq_left hj]
      linarith [mul_nonneg (hEigenvalue j) (hb j)]
    · have hΛj : Λ ≤ eigenvalue j := le_of_lt (lt_of_not_ge (fun h => hj ((hcut j).2 h)))
      simpa [low, hj] using mul_le_mul_of_nonneg_right hΛj (hb j)
  have hsum := (Summable.mul_left Λ hsumb).tsum_le_tsum hpoint
    (hsumenergy.add hsumlow)
  have hlowvalue : (∑' j, low j) = Λ * (∑ j ∈ s, b j) := by
    rw [tsum_eq_sum hlowzero]
    simp [low, ← Finset.mul_sum]
  have hsum' : Λ * (∑' j, b j) ≤
      (∑' j, eigenvalue j * b j) + Λ * (∑ j ∈ s, b j) := by
    simpa only [hsumb.tsum_mul_left, hsumenergy.tsum_add hsumlow, hlowvalue] using hsum
  apply (mul_le_mul_iff_right₀ hΛ).mp
  have hcancel : Λ * ((∑' j, b j) - (∑' j, eigenvalue j * b j) / Λ) =
      Λ * (∑' j, b j) - (∑' j, eigenvalue j * b j) := by
    field_simp [ne_of_gt hΛ]
  rw [hcancel]
  linarith

/-- Summable coefficient version of the counting conclusion in manuscript
Lemma `lem:sp-frame`, when the spectrum below the cutoff is finite.

Taking `ι = ℕ` and `M = R*C` yields the exact algebraic counting bound in the
manuscript. The hypotheses still explicitly require the coefficients,
summability, energy inequality, upper frame bound, and finiteness of the
cutoff spectrum. No spherical generator or eigenbasis is constructed here. -/
theorem summable_weighted_spectral_count {ι : Type*} (s : Finset ι) (eigenvalue b : ι → ℝ)
    (r Λ M : ℝ) (hcut : ∀ j, j ∈ s ↔ eigenvalue j ≤ Λ)
    (hb : ∀ j, 0 ≤ b j) (hEigenvalue : ∀ j, 0 ≤ eigenvalue j) (hbound : ∀ j, b j ≤ M)
    (hM : 0 < M) (hr : 0 ≤ r) (hrΛ : r < Λ)
    (hsumb : Summable b) (hsumenergy : Summable (fun j => eigenvalue j * b j))
    (henergy : (∑' j, eigenvalue j * b j) ≤ r * (∑' j, b j)) :
    (1 - r / Λ) * (∑' j, b j) / M ≤ (s.card : ℝ) := by
  classical
  have hΛ : 0 < Λ := lt_of_le_of_lt hr hrΛ
  have henergy' : (∑' j, eigenvalue j * b j) / Λ ≤ r * (∑' j, b j) / Λ :=
    (div_le_div_iff_of_pos_right hΛ).2 henergy
  have hmass : (1 - r / Λ) * (∑' j, b j) ≤ ∑ j ∈ s, b j := by
    have hlow := summable_low_spectral_mass s eigenvalue b Λ hΛ hcut hb hEigenvalue hsumb hsumenergy
    calc
      (1 - r / Λ) * (∑' j, b j) = (∑' j, b j) - r * (∑' j, b j) / Λ := by ring
      _ ≤ (∑' j, b j) - (∑' j, eigenvalue j * b j) / Λ := by linarith
      _ ≤ _ := hlow
  have hupper : (∑ j ∈ s, b j) ≤ (s.card : ℝ) * M := by
    calc
      (∑ j ∈ s, b j) ≤ ∑ _j ∈ s, M := Finset.sum_le_sum (fun j _ => hbound j)
      _ = _ := by simp
  exact (div_le_iff₀ hM).2 (hmass.trans hupper)

end SlowEquilibration
