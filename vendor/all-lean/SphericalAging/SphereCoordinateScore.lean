module

public import SphericalAging.SphereCarreDuChamp
public import SphericalAging.SphereFisherCurrent

public section

/-! Actual coordinate observables identify the canonical FDT current with the
physical conditional-mean/tangent-score inner product. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereCoordinateScore

open FiniteModel HardSphereDynamics SphericalIntegrationByParts SphereEntropyDissipation
open SphereRotationGeometry SphereGeneratorIntegrationByParts SphereCarreDuChamp SphereFisherCurrent
open scoped InnerProductSpace BigOperators

@[expose] def coordinateObservable {N : ℕ} (i : Fin N) (x : Vector N) : ℝ := x i

theorem coordinateObservable_contDiff {N : ℕ} (i : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateObservable i) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff

theorem coordinateObservable_gradient {N : ℕ} (i : Fin N) (x : Vector N) :
    gradient (coordinateObservable i) x=basisVector i := by
  have he : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i)=
      (InnerProductSpace.toDual ℝ (Vector N)) (basisVector i) := by
    ext y
    simp [basisVector,InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_left]
  unfold gradient coordinateObservable
  change (InnerProductSpace.toDual ℝ (Vector N)).symm
    (fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i) x)=basisVector i
  rw [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).hasFDerivAt.fderiv,he]
  exact (InnerProductSpace.toDual ℝ (Vector N)).symm_apply_apply (basisVector i)

/-- Exact canonical score pairing with one coordinate, using the actual sphere constraint. -/
theorem canonicalGamma_coordinate {N : ℕ} (hN : 0<N) (f : Vector N → ℝ)
    (x : Vector N) (hx : OnSphere x) (i : Fin N) :
    rotationGamma (1/(2*(N : ℝ)))
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f (coordinateObservable i) x=
      (projection x (gradient f x)) i := by
  rw [canonical_rotationGamma hN _ _ _ hx,coordinateObservable_gradient,
    ← projection_self_adjoint,projection_idempotent (Nat.ne_of_gt hN) x _ hx,basis_inner]

/-- Summing genuine coordinate currents gives the exact source vector inner product. -/
theorem coordinate_current_inner {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    (ρ : Vector N → ℝ) (m : Vector N) (x : Vector N) (hx : OnSphere x) :
    (∑ i : Fin N,m i*rotationGamma (1/(2*(N : ℝ)))
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2)
      (relativeLog β J ρ) (coordinateObservable i) x)=
      ⟪m,tangentScore β J ρ x⟫_ℝ := by
  simp_rw [canonicalGamma_coordinate hN _ _ hx]
  exact (real_inner_coordinates m (tangentScore β J ρ x)).symm

end SphericalAging.SphereCoordinateScore
