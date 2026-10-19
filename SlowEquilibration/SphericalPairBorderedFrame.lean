-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairPlaneDirection
public import SlowEquilibration.IntrinsicGradientRegression

/-! Genuine complete tangent bases obtained by adding the geometric plane
direction to the entire N−2 common tangent space. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open Function Module SphericalModel SphericalGaussianJet SphericalForm IntrinsicGradientRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma orthonormal_fin_cons {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (e : Fin m → E) (he : Orthonormal ℝ e) (v : E) (hv : ‖v‖=1)
    (hc : ∀ i,inner ℝ (e i) v=0) : Orthonormal ℝ (Fin.cons v e) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.cases ?_ (fun i=>?_) i
  · refine Fin.cases ?_ (fun j=>?_) j
    · simp only [Fin.cons_zero,ite_true,real_inner_self_eq_norm_sq,hv,one_pow]
    · simpa only [Fin.cons_zero,Fin.cons_succ,Ne.symm (Fin.succ_ne_zero j),ite_false,real_inner_comm v] using hc j
  · refine Fin.cases ?_ (fun j=>?_) j
    · simpa only [Fin.cons_zero,Fin.cons_succ,Fin.succ_ne_zero,ite_false] using hc i
    · simpa only [Fin.cons_succ,Fin.succ_inj] using orthonormal_iff_ite.mp he i j

def borderedFrame {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ))
    (hr : |overlap x y| < 1) : Fin (n+1) → Vector (n+2) :=
  Fin.cons (planeDirection x y) (commonFrame (by omega) x y hx hy hr)

lemma borderedFrame_orthonormal {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ))
    (hr : |overlap x y| < 1) :
    Orthonormal ℝ (borderedFrame x y hx hy hr) := by
  apply orthonormal_fin_cons _ (commonFrame_orthonormal (by omega) x y hx hy hr) _
    (planeDirection_norm (by omega) x y hx hy hr)
  intro i
  exact planeDirection_common_inner x y _ (commonFrame_tangent_left (by omega) x y hx hy hr i)
    (commonFrame_tangent_right (by omega) x y hx hy hr i)

lemma borderedFrame_tangent {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ))
    (hr : |overlap x y| < 1) (i : Fin (n+1)) :
    inner ℝ (borderedFrame x y hx hy hr i) x=0 := by
  refine Fin.cases ?_ (fun i=>?_) i
  · exact planeDirection_tangent (by omega) x y hx
  · exact commonFrame_tangent_left (by omega) x y hx hy hr i

def borderedTangentVector {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ))
    (hr : |overlap x y| < 1) : Fin (n+1) → tangentPlane x :=
  fun i=>⟨borderedFrame x y hx hy hr i,by
    change borderedFrame x y hx hy hr i ∈ (ℝ ∙ x)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,real_inner_comm]
    exact borderedFrame_tangent x y hx hy hr i⟩

lemma borderedTangentVector_orthonormal {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ))
    (hr : |overlap x y| < 1) :
    Orthonormal ℝ (borderedTangentVector x y hx hy hr) := by
  simpa only [orthonormal_iff_ite,Submodule.coe_inner,borderedTangentVector] using
    borderedFrame_orthonormal x y hx hy hr

/-- Complete basis, including the N=2 empty-common-space case; spanning
is derived from genuine tangent dimension and orthonormal independence. -/
def borderedTangentBasis {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ))
    (hr : |overlap x y| < 1) : OrthonormalBasis (Fin (n+1)) ℝ (tangentPlane x) :=
  OrthonormalBasis.mk (borderedTangentVector_orthonormal x y hx hy hr) (by
    have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range (borderedTangentVector x y hx hy hr)))=
        Module.finrank ℝ (tangentPlane x) := by
      rw [finrank_span_eq_card (borderedTangentVector_orthonormal x y hx hy hr).linearIndependent,
        Fintype.card_fin,tangentPlane_finrank x hx]
    rw [Submodule.eq_top_of_finrank_eq hdim])

end
end SlowEquilibration.SphericalPairCommonFrame
