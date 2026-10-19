module

public import SphericalAging.SphereGeneratorIntegrationByParts
public import SphericalAging.SphereRotationGeometry

public section

/-! Actual canonical rotation carré du champ equals the physical sphere tangent metric. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereCarreDuChamp

open Set MeasureTheory FiniteModel HardSphereDynamics
open SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereRotationGeometry
open scoped InnerProductSpace BigOperators

/-- True polarization of the complete coordinate-rotation metric. -/
theorem coordinate_rotation_bilinear_metric {N : ℕ} (hN : 0<N) (x z w : Vector N)
    (hx : OnSphere x) :
    (1/(2*(N : ℝ)))*(∑ i : Fin N,∑ j : Fin N,
      (x j*z i-x i*z j)*(x j*w i-x i*w j))=
      ⟪projection x z,projection x w⟫_ℝ := by
  have hp := coordinate_rotation_metric hN x (z+w) hx
  have hm := coordinate_rotation_metric hN x (z-w) hx
  have hsplus : (∑ i : Fin N,∑ j : Fin N,(x j*(z+w) i-x i*(z+w) j)^2)=
      (∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)^2)+
      2*(∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)*(x j*w i-x i*w j))+
      (∑ i : Fin N,∑ j : Fin N,(x j*w i-x i*w j)^2) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [PiLp.add_apply]
    ring
  have hsminus : (∑ i : Fin N,∑ j : Fin N,(x j*(z-w) i-x i*(z-w) j)^2)=
      (∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)^2)-
      2*(∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)*(x j*w i-x i*w j))+
      (∑ i : Fin N,∑ j : Fin N,(x j*w i-x i*w j)^2) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [PiLp.sub_apply]
    ring
  have hprojminus : projection x (z-w)=projection x z-projection x w := by
    unfold projection
    rw [inner_sub_right,sub_div,sub_smul]
    module
  rw [hsplus,projection_add,← real_inner_self_eq_norm_sq] at hp
  rw [hsminus,hprojminus,← real_inner_self_eq_norm_sq] at hm
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_comm (projection x z) (projection x w)] at hp hm
  linarith

/-- The canonical carré du champ is exactly the sphere tangent gradient product. -/
theorem canonical_rotationGamma {N : ℕ} (hN : 0<N) (f g : Vector N → ℝ)
    (x : Vector N) (hx : OnSphere x) :
    rotationGamma (1/(2*(N : ℝ)))
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f g x=
      ⟪projection x (gradient f x),projection x (gradient g x)⟫_ℝ := by
  unfold rotationGamma
  rw [Fintype.sum_prod_type]
  simp_rw [lieDerivative_coordinate]
  exact coordinate_rotation_bilinear_metric hN x _ _ hx

end SphericalAging.SphereCarreDuChamp
