-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import SphericalAging.HamiltonianTangentHessianGaussianLaw
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-!
# Genuine Gaussian spatial jets of the finite mixed field

Every variable below is an actual spatial derivative of the tensor Hamiltonian
constructed in `SphericalModel`, under its actual product disorder law.
The pure-block derivative coefficient and covariance identities are imported
from the pinned proof provider, then combined using independent degree blocks.
-/

namespace SlowEquilibration.SphericalGaussianJet

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open SphericalModel
open scoped BigOperators InnerProductSpace NNReal

abbrev PureDisorder (N p : ℕ) := SphericalAging.FiniteModel.Disorder N p
abbrev PureLaw (N p : ℕ) := SphericalAging.FiniteModel.disorderLaw N p
abbrev UpperIndex (k : ℕ) := SphericalAging.HamiltonianTangentHessianGaussianLaw.UpperIndex k

/-- The actual derivative evaluated in an ordered list of directions. -/
def jet {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) (J : Disorder N P) : ℝ :=
  iteratedFDeriv ℝ n (field c J) x a

def pureJetCLM (N p n : ℕ) (x : Vector N) (a : Fin n → Vector N) :
    PureDisorder N p →L[ℝ] ℝ :=
  ∑ I : SphericalAging.FiniteModel.TensorIndex N p,
    SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative n I x a •
      ContinuousLinearMap.proj I

theorem pureJetCLM_apply {N p n : ℕ} (x : Vector N) (a : Fin n → Vector N)
    (J : PureDisorder N p) :
    pureJetCLM N p n x a J =
      iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p J) x a := by
  rw [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_tensorLinear]
  simp [pureJetCLM, SphericalAging.FiniteModel.tensorLinear]

def jetCLM {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) : Disorder N P →L[ℝ] ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) •
    (pureJetCLM N p.val.val n x a).comp (ContinuousLinearMap.proj p)

theorem jet_sum {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) (J : Disorder N P) :
    jet c n x a J = ∑ p : Degree P, Real.sqrt (c p) *
      iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val (J p)) x a := by
  unfold jet
  rw [field_iteratedFDeriv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rfl

@[simp] theorem jetCLM_apply {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) (J : Disorder N P) :
    jetCLM c n x a J = jet c n x a J := by
  simp [jetCLM, pureJetCLM_apply, jet_sum]

theorem jet_hasGaussianLaw {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) :
    HasGaussianLaw (jet c n x a) (disorderLaw N P) := by
  have h := (disorder_hasGaussianLaw N P).map_fun (jetCLM c n x a)
  simpa using h

theorem jet_memLp {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) :
    MemLp (jet c n x a) 2 (disorderLaw N P) :=
  (jet_hasGaussianLaw c n x a).memLp_two

/-- Arbitrary finite families of actual derivatives, at arbitrary points and
arbitrary derivative orders, are jointly Gaussian. -/
theorem jet_jointGaussian {N P : ℕ} (c : Degree P → ℝ)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → Vector N)
    (a : (i : ι) → Fin (n i) → Vector N) :
    HasGaussianLaw (fun J : Disorder N P => fun i => jet c (n i) (x i) (a i) J)
      (disorderLaw N P) := by
  have h := (disorder_hasGaussianLaw N P).map_fun
    (ContinuousLinearMap.pi (fun i => jetCLM c (n i) (x i) (a i)))
  simpa using h

def blockJet {N P : ℕ} (p : Degree P) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) (J : Disorder N P) : ℝ :=
  iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val (J p)) x a

theorem blockJet_memLp {N P : ℕ} (p : Degree P) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) :
    MemLp (blockJet p n x a) 2 (disorderLaw N P) := by
  exact (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp n x a).comp_measurePreserving (measurePreserving_eval
      (fun q : Degree P => PureLaw N q.val.val) p)

theorem blockJet_mean {N P : ℕ} (p : Degree P) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) :
    ∫ J, blockJet p n x a J ∂disorderLaw N P = 0 := by
  unfold blockJet disorderLaw
  rw [integral_comp_eval (μ := fun q : Degree P => PureLaw N q.val.val) (i := p)
    (f := fun J : PureDisorder N p.val.val =>
      iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a)
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp
      (p := p.val.val) n x a).aestronglyMeasurable]
  exact SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_mean n x a

theorem jet_mean {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) :
    ∫ J, jet c n x a J ∂disorderLaw N P = 0 := by
  simp_rw [jet_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    change ∑ p : Degree P, Real.sqrt (c p) *
      (∫ J, blockJet p n x a J ∂disorderLaw N P) = 0
    simp [blockJet_mean]
  · intro p hp
    exact ((blockJet_memLp p n x a).integrable (by norm_num)).const_mul _

theorem blockJet_covariance {N P : ℕ} (p q : Degree P) (n m : ℕ)
    (x y : Vector N) (a : Fin n → Vector N) (b : Fin m → Vector N) :
    cov[blockJet p n x a, blockJet q m y b; disorderLaw N P] =
      if p = q then
        cov[fun J : PureDisorder N p.val.val =>
              iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a,
            fun J => iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) y b;
          PureLaw N p.val.val]
      else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl]
    have hmap := (degree_block_hasLaw (N := N) p).map_eq
    have hcov := covariance_map_fun
      (X := fun J : PureDisorder N p.val.val =>
        iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a)
      (Y := fun J : PureDisorder N p.val.val =>
        iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) y b)
      (by rw [hmap]; exact
        (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp n x a).aestronglyMeasurable)
      (by rw [hmap]; exact
        (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp m y b).aestronglyMeasurable)
      (degree_block_hasLaw p).aemeasurable
    rw [hmap] at hcov
    exact hcov.symm
  · rw [ite_eq_right hpq]
    have hX : Measurable (fun J : PureDisorder N p.val.val =>
        iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a) := by
      have heq : (fun J : PureDisorder N p.val.val =>
          iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a) =
          pureJetCLM N p.val.val n x a := by
        funext J
        exact (pureJetCLM_apply x a J).symm
      rw [heq]
      exact (pureJetCLM N p.val.val n x a).measurable
    have hY : Measurable (fun J : PureDisorder N q.val.val =>
        iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N q.val.val J) y b) := by
      have heq : (fun J : PureDisorder N q.val.val =>
          iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N q.val.val J) y b) =
          pureJetCLM N q.val.val m y b := by
        funext J
        exact (pureJetCLM_apply y b J).symm
      rw [heq]
      exact (pureJetCLM N q.val.val m y b).measurable
    exact ((independent_degree_blocks N P).indepFun hpq |>.comp hX hY).covariance_eq_zero
      (blockJet_memLp p n x a) (blockJet_memLp q m y b)

/-- The actual mixed-jet covariance is the coefficient-weighted sum of the
actual pure-block covariances. Cross-degree contributions vanish by independence. -/
theorem jet_covariance {N P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (n m : ℕ) (x y : Vector N) (a : Fin n → Vector N) (b : Fin m → Vector N) :
    cov[jet c n x a, jet c m y b; disorderLaw N P] =
      ∑ p : Degree P, c p *
        cov[fun J : PureDisorder N p.val.val =>
              iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a,
            fun J => iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) y b;
          PureLaw N p.val.val] := by
  classical
  have heqX : jet c n x a = fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p n x a J :=
    funext (jet_sum c n x a)
  have heqY : jet c m y b = fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p m y b J :=
    funext (jet_sum c m y b)
  rw [heqX, heqY]
  change cov[fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p n x a J,
      fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p m y b J; disorderLaw N P] = _
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right, blockJet_covariance]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_eq_single p]
    · simp only [ite_true]
      have hroot : Real.sqrt (c p) * Real.sqrt (c p) = c p := Real.mul_self_sqrt (hc p)
      rw [← mul_assoc, hroot]
    · intro q hq hqp
      simp [Ne.symm hqp]
    · simp
  · intro p
    exact (blockJet_memLp p n x a).const_mul _
  · intro p
    exact (blockJet_memLp p m y b).const_mul _

/-- The ordinary second derivative covariance polynomial. -/
def secondCovariance {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P, c p * (p.val.val : ℝ) * ((p.val.val : ℝ) - 1) * r ^ (p.val.val - 2)

/-- An actual bilinear Euclidean Hessian entry in the chosen tangent frame. -/
def hessianEntry {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (i j : Fin k) (J : Disorder N P) : ℝ :=
  jet c 2 x ![e i, e j] J

theorem hessianEntry_eq_fderiv {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (i j : Fin k) (J : Disorder N P) :
    hessianEntry c x e i j J = fderiv ℝ (fderiv ℝ (field c J)) x (e i) (e j) := by
  simp only [hessianEntry, jet, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]

def upperEntries {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (J : Disorder N P) : UpperIndex k → ℝ :=
  fun ij => hessianEntry c x e ij.val.1 ij.val.2 J

/-- All mixed Hessian upper entries are jointly Gaussian under the original
ordered product disorder, before any matrix-law identification. -/
theorem upperEntries_jointGaussian {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) :
    HasGaussianLaw (upperEntries c x e) (disorderLaw N P) :=
  jet_jointGaussian c (fun _ : UpperIndex k => 2) (fun _ => x)
    (fun ij => ![e ij.val.1, e ij.val.2])

/-- The complete covariance of actual tangent Hessian entries is the GOE
Kronecker-delta kernel, at the exact `xi''(r)/N` normalization. -/
theorem hessianEntry_covariance {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖ ^ 2 = (N : ℝ) * r) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) (i j l m : Fin k) :
    cov[hessianEntry c x e i j, hessianEntry c x e l m; disorderLaw N P] =
      (secondCovariance c r / (N : ℝ)) *
        ((if i = l then 1 else 0) * (if j = m then 1 else 0) +
          (if i = m then 1 else 0) * (if j = l then 1 else 0)) := by
  classical
  unfold hessianEntry
  rw [jet_covariance c hc]
  have hpure (p : Degree P) :
      cov[fun J : PureDisorder N p.val.val =>
          iteratedFDeriv ℝ 2 (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x ![e i, e j],
        fun J => iteratedFDeriv ℝ 2
          (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x ![e l, e m]; PureLaw N p.val.val] =
      ((p.val.val : ℝ) * ((p.val.val : ℝ) - 1) * r ^ (p.val.val - 2) / (N : ℝ)) *
        ((if i = l then 1 else 0) * (if j = m then 1 else 0) +
          (if i = m then 1 else 0) * (if j = l then 1 else 0)) := by
    have h := SphericalAging.HamiltonianTangentHessianGaussianLaw.actual_entry_covariance
      (p := p.val.val) hN (by omega) x hx e he htan i j l m
    change cov[fun J : PureDisorder N p.val.val =>
        fderiv ℝ (fderiv ℝ (SphericalAging.FiniteModel.Hamiltonian N p.val.val J)) x (e i) (e j),
      fun J => fderiv ℝ (fderiv ℝ (SphericalAging.FiniteModel.Hamiltonian N p.val.val J)) x (e l) (e m);
      PureLaw N p.val.val] = _ at h
    simpa only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  simp_rw [hpure]
  unfold secondCovariance
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The upper entries are mutually independent, including diagonal entries. -/
theorem upperEntries_independent {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖ ^ 2 = (N : ℝ) * r) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) :
    iIndepFun (fun ij : UpperIndex k => fun J => upperEntries c x e J ij)
      (disorderLaw N P) := by
  apply (upperEntries_jointGaussian c x e).iIndepFun_of_covariance_eq_zero
  intro a b hab
  change cov[hessianEntry c x e a.val.1 a.val.2,
    hessianEntry c x e b.val.1 b.val.2; disorderLaw N P] = 0
  rw [hessianEntry_covariance hN c hc x hx e he htan,
    SphericalAging.HamiltonianTangentHessianGaussianLaw.upperIndex_covariance_factor_zero a b hab,
    mul_zero]

/-- GOE entry variance: twice as large on the diagonal. -/
def entryVariance {P k : ℕ} (N : ℕ) (c : Degree P → ℝ) (r : ℝ)
    (ij : UpperIndex k) : ℝ≥0 :=
  ((secondCovariance c r / (N : ℝ)) *
    (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal

theorem upperEntry_hasLaw {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖ ^ 2 = (N : ℝ) * r) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) (ij : UpperIndex k) :
    HasLaw (fun J : Disorder N P => upperEntries c x e J ij)
      (gaussianReal 0 (entryVariance N c r ij)) (disorderLaw N P) := by
  classical
  have hg := (upperEntries_jointGaussian c x e).eval ij
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  have hmean : ∫ J, upperEntries c x e J ij ∂disorderLaw N P = 0 :=
    jet_mean c 2 x ![e ij.val.1, e ij.val.2]
  rw [hmean]
  congr 1
  apply congrArg Real.toNNReal
  rw [← covariance_self hg.aemeasurable]
  change cov[hessianEntry c x e ij.val.1 ij.val.2,
    hessianEntry c x e ij.val.1 ij.val.2; disorderLaw N P] = _
  rw [hessianEntry_covariance hN c hc x hx e he htan]
  by_cases hdiag : ij.val.1 = ij.val.2
  · norm_num [hdiag]
  · norm_num [hdiag, Ne.symm hdiag]

/-- The full actual mixed tangent Hessian upper-triangle law is a product
of the independent Gaussian GOE entries, with no GOE law as a premise. -/
theorem tangent_hessian_upper_product_law {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖ ^ 2 = (N : ℝ) * r) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) :
    HasLaw (upperEntries c x e)
      (Measure.pi (fun ij : UpperIndex k => gaussianReal 0 (entryVariance N c r ij)))
      (disorderLaw N P) :=
  (upperEntries_independent hN c hc x hx e he htan).hasLaw_pi
    (upperEntry_hasLaw hN c hc x hx e he htan)

/-- Restriction to finite degree blocks preserves every coefficient-weighted
sum of a canonical mixture, not only its covariance polynomial. -/
theorem mixture_weighted_sum (μ : SlowEquilibration.FiniteMixture) (f : ℕ → ℝ) :
    (∑ p : Degree μ.maxDegree, mixtureCoefficients μ p * f p.val.val) =
      ∑ p ∈ μ.coeff.support, μ.coeff p * f p := by
  classical
  have hsupport : μ.coeff.support ⊆ Finset.range (μ.maxDegree + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (μ.degree_bounds hp).2)
  have hfilter : (∑ p : Fin (μ.maxDegree + 1) with 2 ≤ p.val, μ.coeff p.val * f p.val) =
      ∑ p : Fin (μ.maxDegree + 1), μ.coeff p.val * f p.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs with h
    · rfl
    · rw [μ.zero_below_two p.val (by omega), zero_mul]
  calc
    _ = ∑ p : Fin (μ.maxDegree + 1) with 2 ≤ p.val, μ.coeff p.val * f p.val := by
      simpa [mixtureCoefficients, Degree] using
        (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
          (p := fun p : Fin (μ.maxDegree + 1) => 2 ≤ p.val)
          (fun p => μ.coeff p.val * f p.val))
    _ = ∑ p : Fin (μ.maxDegree + 1), μ.coeff p.val * f p.val := hfilter
    _ = ∑ p ∈ Finset.range (μ.maxDegree + 1), μ.coeff p * f p :=
      Fin.sum_univ_eq_sum_range (fun p => μ.coeff p * f p) _
    _ = _ := (Finsupp.sum_of_support_subset μ.coeff hsupport (fun p c => c * f p)
      (by simp)).symm

/-- The GOE covariance parameter is the genuine ordinary second derivative
of the canonical mixture used throughout the manuscript. -/
theorem secondCovariance_mixture (μ : SlowEquilibration.FiniteMixture) (r : ℝ) :
    secondCovariance (mixtureCoefficients μ) r = μ.xi2 r := by
  unfold secondCovariance
  have h := mixture_weighted_sum μ
    (fun p => (p : ℝ) * ((p : ℝ) - 1) * r ^ (p - 2))
  calc
    _ = ∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ) * ((p : ℝ) - 1) * r ^ (p - 2) := by
      simpa only [mul_assoc] using h
    _ = μ.xi2 r := by
      unfold SlowEquilibration.FiniteMixture.xi2 SlowEquilibration.FiniteMixture.curvatureCoeff
      apply Finset.sum_congr rfl
      intro p hp
      have hp2 := μ.degree_ge_two hp
      rw [Nat.cast_sub (show 1 ≤ p by omega)]
      norm_num

/-- Homogeneity is a pathwise statement about the realized ordered tensor. -/
theorem pure_spatial_smul {N p : ℕ} (J : PureDisorder N p) (x : Vector N) (a : ℝ) :
    SphericalAging.FiniteModel.Hamiltonian N p J (a • x) =
      a ^ p * SphericalAging.FiniteModel.Hamiltonian N p J x := by
  rw [SphericalAging.LandscapeDerivatives.Hamiltonian_eq_diagonal,
    SphericalAging.LandscapeDerivatives.Hamiltonian_eq_diagonal]
  have hm := (SphericalAging.GaussianLandscape.tensorForm N p J).map_smul_univ
    (fun _ => a) (fun _ => x)
  rw [hm]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The exact covariance coefficients of the homothetically rescaled center
field `H_Q(u) = H_N(sqrt(Q) u)`. -/
def centerCoefficients {P : ℕ} (c : Degree P → ℝ) (Q : ℝ) : Degree P → ℝ :=
  fun p => c p * Q ^ p.val.val

theorem centerCoefficients_nonnegative {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∀ p, 0 ≤ centerCoefficients c Q p := fun p => mul_nonneg (hc p) (pow_nonneg hQ _)

theorem sqrt_centerCoefficients {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {Q : ℝ} (hQ : 0 ≤ Q) (p : Degree P) :
    Real.sqrt (centerCoefficients c Q p) = Real.sqrt (c p) * Real.sqrt Q ^ p.val.val := by
  apply (Real.sqrt_eq_iff_eq_sq
    (centerCoefficients_nonnegative c hc hQ p)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))).mpr
  unfold centerCoefficients
  rw [mul_pow, Real.sq_sqrt (hc p), ← pow_mul, Nat.mul_comm p.val.val 2,
    pow_mul, Real.sq_sqrt hQ]

/-- Exact pathwise realization of the manuscript's center field, not merely
a new Gaussian field with a matching covariance. -/
theorem field_center_scale {N P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {Q : ℝ} (hQ : 0 ≤ Q) (J : Disorder N P) (x : Vector N) :
    field (centerCoefficients c Q) J x = field c J (Real.sqrt Q • x) := by
  unfold field blockField
  apply Finset.sum_congr rfl
  intro p hp
  rw [sqrt_centerCoefficients c hc hQ, pure_spatial_smul]
  ring

/-- The center Hessian GOE scale is exactly `b_Q = Q^2 xi''(Q)`. -/
theorem secondCovariance_center {P : ℕ} (c : Degree P → ℝ) (Q : ℝ) :
    secondCovariance (centerCoefficients c Q) 1 = Q ^ 2 * secondCovariance c Q := by
  classical
  unfold secondCovariance centerCoefficients
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [one_pow, mul_one]
  have hpow : Q ^ 2 * Q ^ (p.val.val - 2) = Q ^ p.val.val := by
    rw [← pow_add, Nat.add_sub_of_le p.property]
  calc
    _ = c p * (p.val.val : ℝ) * ((p.val.val : ℝ) - 1) * Q ^ p.val.val := by ring
    _ = _ := by rw [← hpow]; ring

/-- Full actual product GOE law for the canonical mixed center Hessian,
at exactly the normalization of `lem:kr-one-point`. -/
theorem center_hessian_upper_product_law {N k : ℕ} (hN : 0 < N)
    (μ : SlowEquilibration.FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    HasLaw (upperEntries (centerCoefficients (mixtureCoefficients μ) Q) u e)
      (Measure.pi (fun ij : UpperIndex k => gaussianReal 0
        (((Q ^ 2 * μ.xi2 Q / (N : ℝ)) *
          (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal)))
      (disorderLaw N μ.maxDegree) := by
  have h := tangent_hessian_upper_product_law hN
    (centerCoefficients (mixtureCoefficients μ) Q)
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ)
    u (r := 1) (by simpa using hu) e he htan
  simpa only [entryVariance, secondCovariance_center, secondCovariance_mixture] using h

/-- A first derivative of a product with two vanishing linear factors is
zero. This supplies the Hessian-gradient covariance cancellation. -/
theorem derivative_double_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (L M : E →L[ℝ] ℝ)
    (hL : L x = 0) (hM : M x = 0) :
    fderiv ℝ (fun y => f y * L y * M y) x = 0 := by
  have h := (hf.hasFDerivAt.mul L.hasFDerivAt).mul M.hasFDerivAt
  change HasFDerivAt (fun y => f y * L y * M y) _ x at h
  simpa only [Pi.mul_apply, hL, hM, zero_smul, zero_mul, mul_zero, add_zero, zero_add] using h.fderiv

/-- Actual pure-block tangent Hessian entries are uncorrelated with the
field value. The coefficient Gram is computed from the ordered tensor. -/
theorem pure_hessian_value_covariance_zero {N p : ℕ} (hp : 2 ≤ p)
    (x u v : Vector N) (hu : inner ℝ u x = 0) (hv : inner ℝ v x = 0) :
    cov[fun J : PureDisorder N p =>
        iteratedFDeriv ℝ 2 (SphericalAging.FiniteModel.Hamiltonian N p J) x ![u, v],
      fun J => iteratedFDeriv ℝ 0 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun i => Fin.elim0 i); PureLaw N p] = 0 := by
  rw [covariance_eq_sub
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 2 x ![u, v])
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 0 x
      (fun i => Fin.elim0 i))]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_mean,
    zero_mul, sub_zero, Pi.mul_apply]
  rw [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_covariance_gram]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative,
    iteratedFDeriv_zero_apply, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (∑ I : SphericalAging.FiniteModel.TensorIndex N p,
    SphericalAging.HamiltonianTangentHessianCovariance.bilinearCoeff I x u v *
      SphericalAging.GaussianIntegrationByParts.hamiltonianCoefficient I x) = 0
  rw [SphericalAging.HamiltonianTangentHessianCovariance.bilinear_coefficient_gram_left hp,
    hu, hv]
  ring

/-- Actual pure-block tangent Hessian entries are uncorrelated with every
directional derivative, including the radial derivative. -/
theorem pure_hessian_gradient_covariance_zero {N p : ℕ} (hp : 2 ≤ p)
    (x u v w : Vector N) (hu : inner ℝ u x = 0) (hv : inner ℝ v x = 0) :
    cov[fun J : PureDisorder N p =>
        iteratedFDeriv ℝ 2 (SphericalAging.FiniteModel.Hamiltonian N p J) x ![u, v],
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun _ => w); PureLaw N p] = 0 := by
  rw [covariance_eq_sub
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 2 x ![u, v])
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 1 x (fun _ => w))]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_mean,
    zero_mul, sub_zero, Pi.mul_apply]
  rw [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_covariance_gram]
  change (∑ I : SphericalAging.FiniteModel.TensorIndex N p,
    SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative 2 I x ![u, v] *
      SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative 1 I x (fun _ => w)) = 0
  have htwo (I : SphericalAging.FiniteModel.TensorIndex N p) :
      SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative 2 I x ![u, v] =
        SphericalAging.HamiltonianTangentHessianCovariance.bilinearCoeff I x u v := by
    simp only [SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative,
      SphericalAging.HamiltonianTangentHessianCovariance.bilinearCoeff, iteratedFDeriv_two_apply,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [htwo]
  let F : Vector N → ℝ := fun y => SphericalAging.FiniteModel.normalization N p ^ 2 *
    (p : ℝ) * ((p : ℝ) - 1) * (inner ℝ x y) ^ (p - 2)
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_const.mul ((contDiff_const.inner ℝ contDiff_id).pow (p - 2))
  have hcoeff : (fun y : Vector N =>
      ∑ I : SphericalAging.FiniteModel.TensorIndex N p,
        SphericalAging.HamiltonianTangentHessianCovariance.bilinearCoeff I x u v *
          SphericalAging.GaussianIntegrationByParts.hamiltonianCoefficient I y) =
      fun y => F y * inner ℝ u y * inner ℝ v y := by
    funext y
    exact SphericalAging.HamiltonianTangentHessianCovariance.bilinear_coefficient_gram_left hp x y u v
  have hder := SphericalAging.HamiltonianDerivativeCovariance.linear_combination_derivative
    (fun I : SphericalAging.FiniteModel.TensorIndex N p =>
      SphericalAging.HamiltonianTangentHessianCovariance.bilinearCoeff I x u v)
    1 x (fun _ => w)
  rw [hcoeff] at hder
  have hzero := derivative_double_zero (hF.differentiable (by simp) x)
    (innerSL ℝ u) (innerSL ℝ v) (by simpa using hu) (by simpa using hv)
  have hzero' : fderiv ℝ (fun y => F y * inner ℝ u y * inner ℝ v y) x = 0 := by
    simpa only [innerSL_apply_apply] using hzero
  rw [iteratedFDeriv_one_apply, hzero', zero_apply] at hder
  exact hder.symm

theorem hessian_value_covariance_zero {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) (i j : Fin k) :
    cov[hessianEntry c x e i j, jet c 0 x (fun i => Fin.elim0 i); disorderLaw N P] = 0 := by
  unfold hessianEntry
  rw [jet_covariance c hc]
  apply Finset.sum_eq_zero
  intro p hp
  rw [pure_hessian_value_covariance_zero p.property x (e i) (e j) (htan i) (htan j), mul_zero]

theorem hessian_gradient_covariance_zero {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) (i j : Fin k) (w : Vector N) :
    cov[hessianEntry c x e i j, jet c 1 x (fun _ => w); disorderLaw N P] = 0 := by
  unfold hessianEntry
  rw [jet_covariance c hc]
  apply Finset.sum_eq_zero
  intro p hp
  rw [pure_hessian_gradient_covariance_zero p.property x (e i) (e j) w (htan i) (htan j), mul_zero]

/-- Field value together with any finite family of actual directional
derivatives; the family may include the radial and all tangent directions. -/
def valueGradient {N P d : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (w : Fin d → Vector N) (J : Disorder N P) : Option (Fin d) → ℝ
  | none => jet c 0 x (fun i => Fin.elim0 i) J
  | some i => jet c 1 x (fun _ => w i) J

def valueGradientCLM {N P d : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (w : Fin d → Vector N) : Disorder N P →L[ℝ] (Option (Fin d) → ℝ) :=
  ContinuousLinearMap.pi (fun i => match i with
    | none => jetCLM c 0 x (fun j => Fin.elim0 j)
    | some j => jetCLM c 1 x (fun _ => w j))

@[simp] theorem valueGradientCLM_apply {N P d : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (w : Fin d → Vector N) (J : Disorder N P) :
    valueGradientCLM c x w J = valueGradient c x w J := by
  funext i
  cases i <;> simp [valueGradientCLM, valueGradient]

/-- The actual full tangent Hessian matrix is independent of the actual
value and all directional gradient observations. In particular this applies
to the value/radial-derivative pair and tangent gradient in `lem:kr-one-point`. -/
theorem hessian_independent_valueGradient {N P k d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) (w : Fin d → Vector N) :
    IndepFun (upperEntries c x e) (valueGradient c x w) (disorderLaw N P) := by
  have hraw := (disorder_hasGaussianLaw N P).map_fun
    ((ContinuousLinearMap.pi (fun ij : UpperIndex k =>
        jetCLM c 2 x ![e ij.val.1, e ij.val.2])).prod (valueGradientCLM c x w))
  have hjoint := hraw.congr
    (Y := fun J : Disorder N P => (upperEntries c x e J, valueGradient c x w J))
    (Filter.Eventually.of_forall (fun J => by
      simp
      funext ij
      rfl))
  apply hjoint.indepFun_of_covariance_eval
  intro ij i
  cases i with
  | none => exact hessian_value_covariance_zero c hc x e htan ij.val.1 ij.val.2
  | some i => exact hessian_gradient_covariance_zero c hc x e htan ij.val.1 ij.val.2 (w i)

/-- Pathwise Euler identity for an actual ordered pure tensor. -/
theorem pure_radial_jet {N p : ℕ} (J : PureDisorder N p) (x : Vector N) :
    iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => x) =
      (p : ℝ) * SphericalAging.FiniteModel.Hamiltonian N p J x := by
  rw [iteratedFDeriv_one_apply,
    (SphericalAging.LandscapeDerivatives.Hamiltonian_hasFDerivAt J x).fderiv]
  simp only [smul_apply, smul_eq_mul, SphericalAging.LandscapeDerivatives.diagonalDerivative_apply]
  have hu (i : Fin p) : Function.update (fun _ => x) i x = fun _ => x := by
    ext j
    simp [Function.update_apply]
  simp_rw [hu]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    SphericalAging.LandscapeDerivatives.Hamiltonian_eq_diagonal]
  ring

/-- The manuscript's radial derivative is the actual directional derivative,
and its degree-weighted representation follows from Euler's identity. -/
theorem radial_jet_sum {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) :
    jet c 1 x (fun _ => x) J = ∑ p : Degree P,
      Real.sqrt (c p) * (p.val.val : ℝ) * blockField p J x := by
  rw [jet_sum]
  simp_rw [pure_radial_jet]
  unfold blockField
  apply Finset.sum_congr rfl
  intro p hp
  ring

def firstCovariance {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P, c p * (p.val.val : ℝ) * r ^ (p.val.val - 1)

theorem firstCovariance_mixture (μ : SlowEquilibration.FiniteMixture) (r : ℝ) :
    firstCovariance (mixtureCoefficients μ) r = μ.xi1 r := by
  simpa only [firstCovariance, SlowEquilibration.FiniteMixture.xi1, mul_assoc] using
    mixture_weighted_sum μ (fun p => (p : ℝ) * r ^ (p - 1))

theorem firstCovariance_center {P : ℕ} (c : Degree P → ℝ) (Q : ℝ) :
    firstCovariance (centerCoefficients c Q) 1 = Q * firstCovariance c Q := by
  classical
  unfold firstCovariance centerCoefficients
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [one_pow, mul_one]
  have hpow : Q * Q ^ (p.val.val - 1) = Q ^ p.val.val := by
    rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ p.val.val by omega)]
  calc
    _ = c p * (p.val.val : ℝ) * Q ^ p.val.val := by ring
    _ = _ := by rw [← hpow]; ring

theorem covariancePolynomial_center_one {P : ℕ} (c : Degree P → ℝ) (Q : ℝ) :
    covariancePolynomial (centerCoefficients c Q) 1 = covariancePolynomial c Q := by
  unfold covariancePolynomial centerCoefficients
  simp

theorem pure_value_covariance_on_sphere {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    cov[fun J : PureDisorder N p => SphericalAging.FiniteModel.Hamiltonian N p J x,
      fun J => SphericalAging.FiniteModel.Hamiltonian N p J x; PureLaw N p] = (N : ℝ) := by
  rw [SphericalAging.FiniteModel.Hamiltonian_probability_covariance hN,
    SphericalAging.FiniteModel.dimension_covariance_scale N p hN hp,
    real_inner_self_eq_norm_sq, hx, div_self (Nat.cast_ne_zero.mpr hN.ne'), one_pow, mul_one]

theorem pure_value_radial_covariance {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 0
        (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun i => Fin.elim0 i),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun _ => x); PureLaw N p] = (N : ℝ) * (p : ℝ) := by
  simp_rw [iteratedFDeriv_zero_apply, pure_radial_jet]
  rw [covariance_const_mul_right, pure_value_covariance_on_sphere hN hp x hx, mul_comm]

theorem pure_radial_covariance {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1
        (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => x),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun _ => x); PureLaw N p] = (N : ℝ) * (p : ℝ) ^ 2 := by
  simp_rw [pure_radial_jet]
  rw [covariance_const_mul_left, covariance_const_mul_right,
    pure_value_covariance_on_sphere hN hp x hx]
  ring

/-- The value/radial covariance is the true first covariance derivative. -/
theorem value_radial_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    cov[jet c 0 x (fun i => Fin.elim0 i), jet c 1 x (fun _ => x); disorderLaw N P] =
      (N : ℝ) * firstCovariance c 1 := by
  classical
  rw [jet_covariance c hc]
  have hpure (p : Degree P) := pure_value_radial_covariance (p := p.val.val)
    hN (by omega) x hx
  simp_rw [hpure]
  unfold firstCovariance
  simp only [one_pow, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem radial_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    cov[jet c 1 x (fun _ => x), jet c 1 x (fun _ => x); disorderLaw N P] =
      (N : ℝ) * (firstCovariance c 1 + secondCovariance c 1) := by
  classical
  rw [jet_covariance c hc]
  have hpure (p : Degree P) := pure_radial_covariance (p := p.val.val)
    hN (by omega) x hx
  simp_rw [hpure]
  unfold firstCovariance secondCovariance
  simp only [one_pow, mul_one]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The exact actual center-field value and radial covariance matrix
`N Sigma_Q` of `lem:kr-one-point`, using canonical ordinary derivatives. -/
theorem center_value_radial_covariances {N : ℕ} (hN : 0 < N)
    (μ : SlowEquilibration.FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    cov[jet c 0 u (fun i => Fin.elim0 i), jet c 0 u (fun i => Fin.elim0 i);
      disorderLaw N μ.maxDegree] = (N : ℝ) * μ.xi Q ∧
    cov[jet c 0 u (fun i => Fin.elim0 i), jet c 1 u (fun _ => u);
      disorderLaw N μ.maxDegree] = (N : ℝ) * (Q * μ.xi1 Q) ∧
    cov[jet c 1 u (fun _ => u), jet c 1 u (fun _ => u);
      disorderLaw N μ.maxDegree] = (N : ℝ) * (Q * μ.xi1 Q + Q ^ 2 * μ.xi2 Q) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc : ∀ p, 0 ≤ c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  refine ⟨?_, ?_, ?_⟩
  · change cov[fun J => field c J u, fun J => field c J u; disorderLaw N μ.maxDegree] = _
    rw [field_covariance hN c hc, overlap_self hN u hu, covariancePolynomial_center_one,
      covariancePolynomial_mixture]
  · rw [value_radial_covariance hN c hc u hu, firstCovariance_center, firstCovariance_mixture]
  · rw [radial_covariance hN c hc u hu, firstCovariance_center, firstCovariance_mixture,
      secondCovariance_center, secondCovariance_mixture]

theorem pure_tangent_gradient_covariance {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x u v : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (hu : inner ℝ u x = 0) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1
        (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => u),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun _ => v); PureLaw N p] = (p : ℝ) * inner ℝ u v := by
  rw [covariance_eq_sub
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 1 x (fun _ => v))]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_mean,
    zero_mul, sub_zero, Pi.mul_apply]
  rw [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_covariance_gram]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative,
    iteratedFDeriv_one_apply]
  rw [SphericalAging.HamiltonianDerivativeCovariance.coefficient_gradient_cross_gram_overlap hN hp,
    real_inner_self_eq_norm_sq, hx, div_self (Nat.cast_ne_zero.mpr hN.ne'), hu]
  simp

/-- Actual mixed tangent gradient covariance, with the normalization
`xi'(1)` and no Gaussian-vector law assumed. -/
theorem tangent_gradient_covariance {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (x u v : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (hu : inner ℝ u x = 0) :
    cov[jet c 1 x (fun _ => u), jet c 1 x (fun _ => v); disorderLaw N P] =
      firstCovariance c 1 * inner ℝ u v := by
  classical
  rw [jet_covariance c hc]
  have hpure (p : Degree P) := pure_tangent_gradient_covariance (p := p.val.val)
    hN p.property x u v hx hu
  simp_rw [hpure]
  unfold firstCovariance
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

def tangentGradientCoordinates {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (J : Disorder N P) : Fin k → ℝ :=
  fun i => jet c 1 x (fun _ => e i) J

theorem tangentGradientCoordinates_jointGaussian {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) :
    HasGaussianLaw (tangentGradientCoordinates c x e) (disorderLaw N P) :=
  jet_jointGaussian c (fun _ : Fin k => 1) (fun _ => x) (fun i _ => e i)

theorem tangentGradientCoordinates_independent {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) (e : Fin k → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    iIndepFun (fun i => fun J => tangentGradientCoordinates c x e J i) (disorderLaw N P) := by
  apply (tangentGradientCoordinates_jointGaussian c x e).iIndepFun_of_covariance_eq_zero
  intro i j hij
  change cov[jet c 1 x (fun _ => e i), jet c 1 x (fun _ => e j); disorderLaw N P] = 0
  rw [tangent_gradient_covariance hN c hc x (e i) (e j) hx (htan i),
    (orthonormal_iff_ite.mp he), ite_eq_right hij, mul_zero]

theorem tangentGradientCoordinate_hasLaw {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) (e : Fin k → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀ i, inner ℝ (e i) x = 0) (i : Fin k) :
    HasLaw (fun J : Disorder N P => tangentGradientCoordinates c x e J i)
      (gaussianReal 0 (firstCovariance c 1).toNNReal) (disorderLaw N P) := by
  have hg := (tangentGradientCoordinates_jointGaussian c x e).eval i
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  have hmean : ∫ J, tangentGradientCoordinates c x e J i ∂disorderLaw N P = 0 :=
    jet_mean c 1 x (fun _ => e i)
  rw [hmean]
  congr 1
  apply congrArg Real.toNNReal
  rw [← covariance_self hg.aemeasurable]
  change cov[jet c 1 x (fun _ => e i), jet c 1 x (fun _ => e i); disorderLaw N P] = _
  rw [tangent_gradient_covariance hN c hc x (e i) (e i) hx (htan i),
    (orthonormal_iff_ite.mp he)]
  simp

/-- The actual tangent gradient has independent equal-variance Gaussian
coordinates, hence exactly the standard Gaussian-vector law scaled by its
true variance parameter. -/
theorem tangentGradientCoordinates_product_law {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) (e : Fin k → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    HasLaw (tangentGradientCoordinates c x e)
      (Measure.pi (fun _ : Fin k => gaussianReal 0 (firstCovariance c 1).toNNReal))
      (disorderLaw N P) :=
  (tangentGradientCoordinates_independent hN c hc x hx e he htan).hasLaw_pi
    (tangentGradientCoordinate_hasLaw hN c hc x hx e he htan)

theorem center_tangentGradientCoordinates_product_law {N k : ℕ} (hN : 0 < N)
    (μ : SlowEquilibration.FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    HasLaw (tangentGradientCoordinates (centerCoefficients (mixtureCoefficients μ) Q) u e)
      (Measure.pi (fun _ : Fin k => gaussianReal 0 (Q * μ.xi1 Q).toNNReal))
      (disorderLaw N μ.maxDegree) := by
  have h := tangentGradientCoordinates_product_law hN
    (centerCoefficients (mixtureCoefficients μ) Q)
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ) u hu e he htan
  simpa only [firstCovariance_center, firstCovariance_mixture] using h

theorem pure_value_gradient_covariance_zero {N p : ℕ}
    (x u : Vector N) (hu : inner ℝ u x = 0) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 0
        (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun i => Fin.elim0 i),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun _ => u); PureLaw N p] = 0 := by
  rw [covariance_comm]
  rw [covariance_eq_sub
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp 0 x
      (fun i => Fin.elim0 i))]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_mean,
    zero_mul, sub_zero, Pi.mul_apply]
  rw [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_covariance_gram]
  simp only [SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
  rw [SphericalAging.HamiltonianDerivativeCovariance.coefficient_gradient_gram_left,
    hu, mul_zero]

theorem pure_radial_gradient_covariance_zero {N p : ℕ}
    (x u : Vector N) (hu : inner ℝ u x = 0) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1
        (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => x),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x
        (fun _ => u); PureLaw N p] = 0 := by
  have h := pure_value_gradient_covariance_zero (p := p) x u hu
  simp_rw [iteratedFDeriv_zero_apply] at h
  simp_rw [pure_radial_jet]
  rw [covariance_const_mul_left, h, mul_zero]

theorem value_tangent_gradient_covariance_zero {N P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x u : Vector N) (hu : inner ℝ u x = 0) :
    cov[jet c 0 x (fun i => Fin.elim0 i), jet c 1 x (fun _ => u); disorderLaw N P] = 0 := by
  rw [jet_covariance c hc]
  apply Finset.sum_eq_zero
  intro p hp
  rw [pure_value_gradient_covariance_zero x u hu, mul_zero]

theorem radial_tangent_gradient_covariance_zero {N P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x u : Vector N) (hu : inner ℝ u x = 0) :
    cov[jet c 1 x (fun _ => x), jet c 1 x (fun _ => u); disorderLaw N P] = 0 := by
  rw [jet_covariance c hc]
  apply Finset.sum_eq_zero
  intro p hp
  rw [pure_radial_gradient_covariance_zero x u hu, mul_zero]

/-- The actual value/radial pair is independent of the actual tangent
gradient coordinates, completing the cross-block independence calculation. -/
theorem valueRadial_independent_tangentGradient {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    IndepFun (valueGradient c x (fun _ : Fin 1 => x))
      (tangentGradientCoordinates c x e) (disorderLaw N P) := by
  have hraw := (disorder_hasGaussianLaw N P).map_fun
    ((valueGradientCLM c x (fun _ : Fin 1 => x)).prod
      (ContinuousLinearMap.pi (fun i : Fin k => jetCLM c 1 x (fun _ => e i))))
  have hjoint := hraw.congr
    (Y := fun J : Disorder N P =>
      (valueGradient c x (fun _ : Fin 1 => x) J, tangentGradientCoordinates c x e J))
    (Filter.Eventually.of_forall (fun J => by
      simp
      rfl))
  apply hjoint.indepFun_of_covariance_eval
  intro a i
  cases a with
  | none => exact value_tangent_gradient_covariance_zero c hc x (e i) (htan i)
  | some a => exact radial_tangent_gradient_covariance_zero c hc x (e i) (htan i)

theorem hessianEntry_symm {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (i j : Fin k) (J : Disorder N P) :
    hessianEntry c x e i j J = hessianEntry c x e j i J := by
  rw [hessianEntry_eq_fderiv, hessianEntry_eq_fderiv]
  exact (field_contDiff c J).contDiffAt.isSymmSndFDerivAt (by simp) (e i) (e j)

/-- The literal symmetric matrix of the actual compressed Euclidean Hessian. -/
def hessianMatrix {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) (J : Disorder N P) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => hessianEntry c x e i j J

/-- Reconstruct a symmetric matrix from its upper triangle. -/
def symmetricMatrix {k : ℕ} (a : UpperIndex k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

theorem symmetricMatrix_measurable (k : ℕ) : Measurable (symmetricMatrix (k := k)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold symmetricMatrix
  split_ifs <;> exact measurable_pi_apply _

/-- A genuine GOE law constructed as a symmetric matrix of independent
centered Gaussian upper entries, with off-diagonal variance `s/N`. -/
def goeLaw (k N : ℕ) (s : ℝ) : Measure (Matrix (Fin k) (Fin k) ℝ) :=
  (Measure.pi (fun ij : UpperIndex k => gaussianReal 0
    (((s / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal))).map symmetricMatrix

theorem hessianMatrix_eq_symmetricMatrix {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (J : Disorder N P) :
    hessianMatrix c x e J = symmetricMatrix (upperEntries c x e J) := by
  ext i j
  unfold hessianMatrix symmetricMatrix
  split_ifs
  · rfl
  · exact hessianEntry_symm c x e i j J

/-- The full actual symmetric Hessian matrix has the constructed GOE law;
this is a complete matrix law rather than an entrywise surrogate. -/
theorem tangent_hessian_matrix_hasLaw {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖ ^ 2 = (N : ℝ) * r) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) :
    HasLaw (hessianMatrix c x e) (goeLaw k N (secondCovariance c r)) (disorderLaw N P) := by
  have h := (hasLaw_map (P := Measure.pi (fun ij : UpperIndex k =>
      gaussianReal 0 (entryVariance N c r ij))) (symmetricMatrix_measurable k).aemeasurable).comp
    (tangent_hessian_upper_product_law hN c hc x hx e he htan)
  apply h.congr
  exact Filter.Eventually.of_forall (fun J => hessianMatrix_eq_symmetricMatrix c x e J)

theorem center_hessian_matrix_hasLaw {N k : ℕ} (hN : 0 < N)
    (μ : SlowEquilibration.FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    HasLaw (hessianMatrix (centerCoefficients (mixtureCoefficients μ) Q) u e)
      (goeLaw k N (Q ^ 2 * μ.xi2 Q)) (disorderLaw N μ.maxDegree) := by
  have h := tangent_hessian_matrix_hasLaw hN
    (centerCoefficients (mixtureCoefficients μ) Q)
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ)
    u (r := 1) (by simpa using hu) e he htan
  simpa only [secondCovariance_center, secondCovariance_mixture] using h

theorem valueGradient_aemeasurable {N P d : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (w : Fin d → Vector N) : AEMeasurable (valueGradient c x w) (disorderLaw N P) := by
  apply aemeasurable_pi_iff.mpr
  intro i
  cases i with
  | none => exact (jet_hasGaussianLaw c 0 x (fun j => Fin.elim0 j)).aemeasurable
  | some i => exact (jet_hasGaussianLaw c 1 x (fun _ => w i)).aemeasurable

instance goeLaw_probability (k N : ℕ) (s : ℝ) : IsProbabilityMeasure (goeLaw k N s) := by
  unfold goeLaw
  exact (hasLaw_map (P := Measure.pi (fun ij : UpperIndex k => gaussianReal 0
      (((s / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal)))
    (symmetricMatrix_measurable k).aemeasurable).isProbabilityMeasure_iff.mp inferInstance

/-- The GOE marginal admits this explicit everywhere-defined constant
conditional kernel. This is a kernel for the Hessian marginal; it does not
assert that the whole-field coefficient regression version has been built. -/
def hessianConditionalKernel (k d N : ℕ) (s : ℝ) :
    Kernel (Option (Fin d) → ℝ) (Matrix (Fin k) (Fin k) ℝ) :=
  Kernel.const _ (goeLaw k N s)

instance hessianConditionalKernel_markov (k d N : ℕ) (s : ℝ) :
    IsMarkovKernel (hessianConditionalKernel k d N s) := by
  unfold hessianConditionalKernel
  infer_instance

/-- A genuine disintegration identity for the actual observed-value/gradient
and actual Hessian joint law. The explicit kernel is defined at every target,
including zero-gradient targets, and has the GOE law there. -/
theorem hessian_marginal_conditional_disintegration {N P k d : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖ ^ 2 = (N : ℝ) * r) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) (w : Fin d → Vector N) :
    ((disorderLaw N P).map (valueGradient c x w)) ⊗ₘ
        hessianConditionalKernel k d N (secondCovariance c r) =
      (disorderLaw N P).map (fun J => (valueGradient c x w J, hessianMatrix c x e J)) := by
  have hmatLaw := tangent_hessian_matrix_hasLaw hN c hc x hx e he htan
  have hcomp := (hessian_independent_valueGradient c hc x e htan w).symm.comp
    measurable_id (symmetricMatrix_measurable k)
  have heq : (fun J : Disorder N P => symmetricMatrix (upperEntries c x e J)) =
      hessianMatrix c x e := by
    funext J
    exact (hessianMatrix_eq_symmetricMatrix c x e J).symm
  change IndepFun (valueGradient c x w)
    (fun J => symmetricMatrix (upperEntries c x e J)) (disorderLaw N P) at hcomp
  rw [heq] at hcomp
  have hprod := hcomp.map_prod_eq_prod_map_map (valueGradient_aemeasurable c x w) hmatLaw.aemeasurable
  unfold hessianConditionalKernel
  rw [Measure.compProd_const]
  rw [hmatLaw.map_eq] at hprod
  exact hprod.symm

/-- The conditional Hessian marginal is exactly GOE at every specified
observation target; no target is discarded as a null set. -/
theorem hessianConditionalKernel_apply (k d N : ℕ) (s : ℝ) (a : Option (Fin d) → ℝ) :
    hessianConditionalKernel k d N s a = goeLaw k N s := rfl

end
end SlowEquilibration.SphericalGaussianJet
