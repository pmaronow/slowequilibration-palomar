-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTwoPointCovariance
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual complete common-complement frame for two noncollinear sphere
points. Its dimension N−2 is derived from the literal two-point Gram. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open Function Module SphericalModel SphericalGaussianJet SphericalTwoPointCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def commonPlane {N : ℕ} (x y : Vector N) : Submodule ℝ (Vector N) :=
  (Submodule.span ℝ (Set.range ![x,y]))ᗮ

lemma sphere_pair_linearIndependent {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    LinearIndependent ℝ ![x,y] := by
  classical
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  have hgram : Matrix.gram ℝ ![x,y]=
      !![(N:ℝ),inner ℝ x y;inner ℝ x y,(N:ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · change inner ℝ x x=(N:ℝ)
      rw [real_inner_self_eq_norm_sq,hx]
    · change inner ℝ x y=inner ℝ x y
      rfl
    · change inner ℝ y x=inner ℝ x y
      exact real_inner_comm x y
    · change inner ℝ y y=(N:ℝ)
      rw [real_inner_self_eq_norm_sq,hy]

  rw [hgram,Matrix.det_fin_two]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [inner_eq_dimension_overlap hN x y]
  have hh : (overlap x y)^2 < 1 := by
    have hsq:=(sq_lt_sq₀ (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ))).mpr hr
    simpa only [sq_abs,one_pow] using hsq
  have hpos : 0 < (N:ℝ)^2*(1-overlap x y^2) := by positivity
  nlinarith

lemma commonPlane_finrank {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    Module.finrank ℝ (commonPlane x y)=N-2 := by
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range ![x,y]))=2 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card (sphere_pair_linearIndependent hN x y hx hy hr)
  have hsum:=(Submodule.span ℝ (Set.range ![x,y])).finrank_add_finrank_orthogonal
  rw [hdim,finrank_euclideanSpace,Fintype.card_fin] at hsum
  change 2+Module.finrank ℝ (commonPlane x y)=N at hsum
  omega

def commonBasis {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    OrthonormalBasis (Fin (N-2)) ℝ (commonPlane x y) :=
  (stdOrthonormalBasis ℝ (commonPlane x y)).reindex (finCongr (commonPlane_finrank hN x y hx hy hr))

def commonFrame {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    Fin (N-2) → Vector N := fun i => commonBasis hN x y hx hy hr i

lemma commonFrame_orthonormal {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    Orthonormal ℝ (commonFrame hN x y hx hy hr) :=
  (commonBasis hN x y hx hy hr).orthonormal.comp_linearIsometry (commonPlane x y).subtypeₗᵢ

lemma commonFrame_tangent_left {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) (i : Fin (N-2)) :
    inner ℝ (commonFrame hN x y hx hy hr i) x=0 := by
  have hm:=(commonBasis hN x y hx hy hr i).property
  have hxmem : x ∈ Submodule.span ℝ (Set.range ![x,y]) :=
    Submodule.subset_span ⟨0,by simp⟩
  exact Submodule.inner_left_of_mem_orthogonal hxmem hm

lemma commonFrame_tangent_right {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) (i : Fin (N-2)) :
    inner ℝ (commonFrame hN x y hx hy hr i) y=0 := by
  have hm:=(commonBasis hN x y hx hy hr i).property
  have hymem : y ∈ Submodule.span ℝ (Set.range ![x,y]) :=
    Submodule.subset_span ⟨1,by simp⟩
  exact Submodule.inner_left_of_mem_orthogonal hymem hm

end
end SlowEquilibration.SphericalPairCommonFrame
