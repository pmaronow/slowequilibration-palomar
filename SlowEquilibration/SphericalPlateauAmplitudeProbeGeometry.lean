-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeKernel
public import SlowEquilibration.SphericalLatitudeFrameParseval
public import SlowEquilibration.SphericalPlateauAmplitudeDiracTrial

@[expose] public section

/-! # Canonical physical geometry of both actual Gaussian probes

The true selected covariance is a polynomial of ordinary physical overlaps.
No latitude normalization or inverse transverse coordinate is used, so the
identities remain valid at the poles and on the whole ambient space.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set SphericalModel GaussianReplicaCalculus
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Physical transverse inner product after the actual canonical projection. -/
theorem latitudeFrameAt_adjoint_normalized_inner (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (u v : Vector (n+1)) :
    (inner ℝ ((latitudeFrameAt x).toContinuousLinearMap.adjoint u)
      ((latitudeFrameAt x).toContinuousLinearMap.adjoint v))/(n+1 : ℝ)=
        overlap u v-overlap x u*overlap x v := by
  rw [latitudeFrameAt_adjoint_inner x hx u v]
  unfold overlap
  rw [real_inner_comm u x,real_inner_comm v x]
  simp only [Nat.cast_add,Nat.cast_one]
  have hN : (n : ℝ)+1≠0 := by positivity
  field_simp

/-- Literal finite source probe polynomial on physical replica overlaps. -/
def amplitudePhysicalProbePolynomial (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (r r' R : ℝ) : ℝ :=
  mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1) : ℝ)*
    (r*r')^(p₀.val.val-(k.val+1))*(R-r*r')^(k.val+1)

/-- Exact selected covariance on every ambient pair, without a sphere
or transverse-normalization premise on the replicas. -/
theorem selectedKernel_amplitudeBankLinear_canonical (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (u v : Vector (n+1)) :
    selectedKernel (amplitudeBankLinear μ β x (latitudeFrameAt x) p₀ (fun _ => 1))
      (amplitudeBankLabel μ p₀ k) u v=
        β^2*((n+1 : ℕ) : ℝ)*amplitudePhysicalProbePolynomial μ p₀ k
          (overlap x u) (overlap x v) (overlap u v) := by
  rw [selectedKernel_amplitudeBankLinear_physical,latitudeFrameAt_adjoint_normalized_inner x hx]
  unfold amplitudePhysicalProbePolynomial
  simp only [Nat.cast_add,Nat.cast_one]
  ring

/-- On the actual physical sphere the diagonal probe is precisely the
literal latitude coefficient used by the fixed original Dirac trial. -/
theorem amplitudePhysicalProbePolynomial_diag (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (r : ℝ) :
    amplitudePhysicalProbePolynomial μ p₀ k r r 1=amplitudeSelectedCoefficient μ p₀ k r := by
  unfold amplitudePhysicalProbePolynomial amplitudeSelectedCoefficient
  rw [show r*r=r^2 by ring,← pow_mul]

/-- The two probe powers at the source center are ordinary first and
second moments of physical overlap minus q². -/
theorem amplitudePhysicalProbePolynomial_center (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (q R : ℝ) :
    amplitudePhysicalProbePolynomial μ p₀ k q q R=
      mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1) : ℝ)*
        q^(2*(p₀.val.val-(k.val+1)))*(R-q^2)^(k.val+1) := by
  unfold amplitudePhysicalProbePolynomial
  rw [show q*q=q^2 by ring,← pow_mul]

theorem amplitudePhysicalProbePolynomial_continuous (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) :
    Continuous (fun z : (ℝ×ℝ)×ℝ => amplitudePhysicalProbePolynomial μ p₀ k z.1.1 z.1.2 z.2) := by
  unfold amplitudePhysicalProbePolynomial
  fun_prop

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
