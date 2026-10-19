-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeAllDisorderRadialMean
public import SlowEquilibration.SphericalLatitudePairedCorrectionBound

/-! Exact finite-degree polynomial and radial derivative of the actual
mixed latitude mean. This is valid for every original tensor sample. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalLatitudeTensorMoments
open scoped RealInnerProductSpace BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem orderedHamiltonian_latitude_integrable {n : ℕ} (hn : 1≤n) (p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    Integrable (SphericalAging.FiniteModel.Hamiltonian (n+1) p J)
      (latitudeLaw u (latitudeFrameAt u) r) := by
  unfold SphericalAging.FiniteModel.Hamiltonian
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro I hI
  exact (actual_latitude_tensorMonomial_integrable hn p u hu hr I).const_mul _

/-- The exact fixed-sample mixed latitude radial polynomial. -/
def originalLatitudeRadialPolynomial {n P : ℕ} (c : Degree P→ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (r : ℝ) : ℝ :=
  ∑ p : Degree P,Real.sqrt (c p)*(r^p.val.val*blockField p J u+
    pairedLatitudeCorrection n p.val.val (J p) u r)

/-- True actual latitude mean, retaining all original Wick corrections. -/
theorem actual_latitudeFieldMean_eq_originalPolynomial {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    latitudeFieldMean c J u (latitudeFrameAt u) r=originalLatitudeRadialPolynomial c J u r := by
  unfold latitudeFieldMean field originalLatitudeRadialPolynomial
  have hi (p : Degree P) : Integrable (fun v : Vector (n+1) => Real.sqrt (c p)*blockField p J v)
      (latitudeLaw u (latitudeFrameAt u) r) :=
    (orderedHamiltonian_latitude_integrable hn p.val.val (J p) u hu hr).const_mul _
  rw [integral_finsetSum _ (fun p _ => hi p)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_const_mul]
  exact congrArg (fun a => Real.sqrt (c p)*a)
    (actual_orderedHamiltonian_latitude_mean_eq_leading_add_correction hn p.val.val (J p) u hu hr)

/-- The literal polynomial derivative, with no differentiation premise
for the actual latitude mean. -/
theorem originalLatitudeRadialPolynomial_hasDerivAt {n P : ℕ} (c : Degree P→ℝ)
    (J : Disorder (n+1) P) (u : Vector (n+1)) (r : ℝ) :
    HasDerivAt (originalLatitudeRadialPolynomial c J u)
      (∑ p : Degree P,Real.sqrt (c p)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u+
        deriv (pairedLatitudeCorrection n p.val.val (J p) u) r)) r := by
  unfold originalLatitudeRadialPolynomial
  apply HasDerivAt.fun_sum
  intro p hp
  have h := pairedLatitudeCorrection_hasDerivAt n p.val.val (J p) u r
  rw [←h.deriv] at h
  exact ((((hasDerivAt_pow p.val.val r).mul_const (blockField p J u)).add h).const_mul (Real.sqrt (c p)))

/-- Exact actual mean of the source tangent observable in the original
field, obtained from its genuine radial mean derivative. -/
theorem actual_latitudeObservableMean_eq_originalPolynomial_derivative {n P : ℕ} (hn : 1≤n)
    (c : Degree P→ℝ) (J : Disorder (n+1) P) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    latitudeObservableMean c J u (latitudeFrameAt u) r=
      (1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
        (∑ p : Degree P,Real.sqrt (c p)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u+
          deriv (pairedLatitudeCorrection n p.val.val (J p) u) r)) := by
  rw [actual_latitudeObservableMean_allDisorder_eq_radial_derivative hn c J u hu
    (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hr]
  have he : latitudeFieldMean c J u (latitudeFrameAt u)=ᶠ[𝓝 r] originalLatitudeRadialPolynomial c J u := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact actual_latitudeFieldMean_eq_originalPolynomial hn c J u hu (abs_lt.mpr ht).le
  rw [((originalLatitudeRadialPolynomial_hasDerivAt c J u r).congr_of_eventuallyEq he).deriv]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
