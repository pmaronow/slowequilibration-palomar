module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalClosability
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology ContDiff

/-- The actual rotation gradient in the finite Hilbert sum of actual Gibbs
L² spaces. Its squared norm is exactly `2N` times the gradient energy. -/
def rotationGradientL2 {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) :=
  WithLp.toLp 2 (fun ij => gibbsToL2 hN β H hH (lieDerivative (coordinateRotation ij.1 ij.2) f)
    (lieDerivative_continuous _ hf))

theorem dirichletEnergy_eq_rotationGradientL2_norm {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    dirichletEnergy N β H f =
      (1 / (2 * (N : ℝ))) * ‖rotationGradientL2 hN β H hH f hf‖ ^ 2 := by
  rw [dirichletEnergy, dirichletForm_eq_rotation_integrals hN β hH hf hf,
    ← real_inner_self_eq_norm_sq]
  congr 1
  rw [PiLp.inner_apply]
  simp only [rotationGradientL2, WithLp.ofLp_toLp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [gibbsToL2_inner]

/-- Closability of the actual full spherical gradient, using its exact
rotation-frame realization in L² of the actual Gibbs measure. -/
theorem rotationGradientL2_closable {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (f : ℕ → Vector N → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (v : PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)))
    (hu : Tendsto (fun n => gibbsToL2 hN β H hH.continuous (f n) (hf n).continuous)
      atTop (𝓝 0))
    (hdu : Tendsto (fun n => rotationGradientL2 hN β H hH.continuous (f n) (hf n))
      atTop (𝓝 v)) : v = 0 := by
  apply PiLp.ext
  intro ij
  have hd := (PiLp.continuous_apply 2
    (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) ij).tendsto v |>.comp hdu
  exact lieDerivative_closable hN β hH (coordinateRotation ij.1 ij.2)
    (coordinateRotation_skew _ _) f hf (v ij) hu hd

/-- The actual smooth ambient core, before quotienting by spherical L²
agreement. The closure below performs that quotient through a graph. -/
def smoothCore (N : ℕ) : Submodule ℝ (Vector N → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by change ContDiff ℝ ∞ (0 : Vector N → ℝ); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    exact hf.const_smul c

@[simp] theorem mem_smoothCore {N : ℕ} (f : Vector N → ℝ) :
    f ∈ smoothCore N ↔ ContDiff ℝ ∞ f := Iff.rfl

theorem smoothCore_contDiff {N : ℕ} (f : smoothCore N) :
    ContDiff ℝ ∞ (f : Vector N → ℝ) := f.property

theorem gibbsToL2_congr {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f g : Vector N → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[gibbsLaw N β H] g) :
    gibbsToL2 hN β H hH f hf = gibbsToL2 hN β H hH g hg :=
  MemLp.toLp_congr _ _ hfg

theorem gibbsToL2_add {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f g : Vector N → ℝ) (hf : Continuous f) (hg : Continuous g) :
    gibbsToL2 hN β H hH (f + g) (hf.add hg) =
      gibbsToL2 hN β H hH f hf + gibbsToL2 hN β H hH g hg := rfl

theorem gibbsToL2_smul {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) (hf : Continuous f) (c : ℝ) :
    gibbsToL2 hN β H hH (c • f) (hf.const_smul c) =
      c • gibbsToL2 hN β H hH f hf := rfl

theorem lieDerivative_add {N : ℕ} (A : Operator N) (f g : Vector N → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    lieDerivative A (f + g) = lieDerivative A f + lieDerivative A g := by
  funext x
  unfold lieDerivative
  rw [fderiv_add (hf x) (hg x)]
  rfl

theorem lieDerivative_smul {N : ℕ} (A : Operator N) (f : Vector N → ℝ)
    (hf : Differentiable ℝ f) (c : ℝ) :
    lieDerivative A (c • f) = c • lieDerivative A f := by
  funext x
  unfold lieDerivative
  rw [fderiv_const_smul (hf x) c]
  rfl

theorem rotationGradientL2_add {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f g : Vector N → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    rotationGradientL2 hN β H hH (f + g) (hf.add hg) =
      rotationGradientL2 hN β H hH f hf + rotationGradientL2 hN β H hH g hg := by
  apply PiLp.ext
  intro ij
  simp only [rotationGradientL2, WithLp.ofLp_toLp, PiLp.add_apply]
  calc
    _ = gibbsToL2 hN β H hH
        (lieDerivative (coordinateRotation ij.1 ij.2) f + lieDerivative (coordinateRotation ij.1 ij.2) g)
        ((lieDerivative_continuous _ hf).add (lieDerivative_continuous _ hg)) := by
      apply gibbsToL2_congr
      apply ae_of_all
      intro x
      exact congrFun (lieDerivative_add _ f g (hf.differentiable (by norm_num))
        (hg.differentiable (by norm_num))) x
    _ = _ := gibbsToL2_add hN β H hH _ _ _ _

theorem rotationGradientL2_smul {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ) :
    rotationGradientL2 hN β H hH (c • f) (hf.const_smul c) =
      c • rotationGradientL2 hN β H hH f hf := by
  apply PiLp.ext
  intro ij
  simp only [rotationGradientL2, WithLp.ofLp_toLp, PiLp.smul_apply]
  calc
    _ = gibbsToL2 hN β H hH (c • lieDerivative (coordinateRotation ij.1 ij.2) f)
        ((lieDerivative_continuous _ hf).const_smul c) := by
      apply gibbsToL2_congr
      apply ae_of_all
      intro x
      exact congrFun (lieDerivative_smul _ f (hf.differentiable (by norm_num)) c) x
    _ = _ := gibbsToL2_smul hN β H hH _ _ c


/-- The scalar needed to represent the literal manuscript energy as a
Hilbert norm squared in the coordinate rotation frame. -/
def gradientScale (N : ℕ) : ℝ := Real.sqrt (1 / (2 * (N : ℝ)))

theorem gradientScale_pos {N : ℕ} (hN : 1 ≤ N) : 0 < gradientScale N := by
  unfold gradientScale
  apply Real.sqrt_pos.mpr
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  positivity

def normalizedRotationGradientL2 {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) :=
  gradientScale N • rotationGradientL2 hN β H hH f hf

theorem dirichletEnergy_eq_normalizedRotationGradientL2_norm {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    dirichletEnergy N β H f = ‖normalizedRotationGradientL2 hN β H hH f hf‖ ^ 2 := by
  rw [dirichletEnergy_eq_rotationGradientL2_norm hN β H hH f hf]
  rw [normalizedRotationGradientL2, norm_smul, Real.norm_eq_abs,
    abs_of_pos (gradientScale_pos hN), mul_pow, gradientScale, Real.sq_sqrt (by positivity)]

theorem normalizedRotationGradientL2_add {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f g : Vector N → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    normalizedRotationGradientL2 hN β H hH (f + g) (hf.add hg) =
      normalizedRotationGradientL2 hN β H hH f hf +
        normalizedRotationGradientL2 hN β H hH g hg := by
  unfold normalizedRotationGradientL2
  rw [rotationGradientL2_add hN β H hH f g hf hg, smul_add]

theorem normalizedRotationGradientL2_smul {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 1 f) (c : ℝ) :
    normalizedRotationGradientL2 hN β H hH (c • f) (hf.const_smul c) =
      c • normalizedRotationGradientL2 hN β H hH f hf := by
  unfold normalizedRotationGradientL2
  rw [rotationGradientL2_smul hN β H hH f hf c]
  simp only [smul_smul]
  rw [mul_comm]

theorem normalizedRotationGradientL2_closable {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (f : ℕ → Vector N → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (v : PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)))
    (hu : Tendsto (fun n => gibbsToL2 hN β H hH.continuous (f n) (hf n).continuous)
      atTop (𝓝 0))
    (hdu : Tendsto (fun n => normalizedRotationGradientL2 hN β H hH.continuous (f n) (hf n))
      atTop (𝓝 v)) : v = 0 := by
  have hs : gradientScale N ≠ 0 := (gradientScale_pos hN).ne'
  have hd := hdu.const_smul (gradientScale N)⁻¹
  have he : (fun n => (gradientScale N)⁻¹ •
      normalizedRotationGradientL2 hN β H hH.continuous (f n) (hf n)) =
      (fun n => rotationGradientL2 hN β H hH.continuous (f n) (hf n)) := by
    funext n
    simp [normalizedRotationGradientL2, smul_smul, hs]
  rw [he] at hd
  have hz := rotationGradientL2_closable hN β hH f hf ((gradientScale N)⁻¹ • v) hu hd
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hs)

/-- The genuine smooth gradient graph in the actual Gibbs L² Hilbert space. -/
def smoothGradientGraphLinear {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : smoothCore N →ₗ[ℝ]
      (WithLp 2 (Lp ℝ 2 (gibbsLaw N β H) ×
        PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)))) where
  toFun f := WithLp.toLp 2 (gibbsToL2 hN β H hH f (smoothCore_contDiff f).continuous,
    normalizedRotationGradientL2 hN β H hH f ((smoothCore_contDiff f).of_le (by simp)))
  map_add' f g := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact gibbsToL2_add hN β H hH f g
        (smoothCore_contDiff f).continuous (smoothCore_contDiff g).continuous
    · exact normalizedRotationGradientL2_add hN β H hH f g
        ((smoothCore_contDiff f).of_le (by simp)) ((smoothCore_contDiff g).of_le (by simp))
  map_smul' c f := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact gibbsToL2_smul hN β H hH f (smoothCore_contDiff f).continuous c
    · exact normalizedRotationGradientL2_smul hN β H hH f ((smoothCore_contDiff f).of_le (by simp)) c

/-- The literal closure of the smooth gradient graph. No weak derivative
existence, spectral conclusion, or injectivity is built into this definition. -/
def sphericalSobolevGraph {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : Submodule ℝ
      (WithLp 2 (Lp ℝ 2 (gibbsLaw N β H) ×
        PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)))) :=
  (LinearMap.range (smoothGradientGraphLinear hN β H hH)).topologicalClosure

/-- The closure is a genuine complete Hilbert graph, constructed from the
actual smooth functions and the actual Gibbs gradient energy. -/
instance sphericalSobolevGraph_complete {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    CompleteSpace (sphericalSobolevGraph hN β H hH) :=
  inferInstanceAs (CompleteSpace
    (LinearMap.range (smoothGradientGraphLinear hN β H hH)).topologicalClosure)

/-- The graph closure has no vertical fiber. This proves closability of the
actual spherical gradient form and makes its completed functions unambiguous
as elements of actual L²(Gibbs). -/
theorem sphericalSobolevGraph_zero_fiber {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H)
    (z : sphericalSobolevGraph hN β H hH.continuous) (hz : z.val.fst = 0) : z.val.snd = 0 := by
  have hm : z.val ∈ closure (Set.range (smoothGradientGraphLinear hN β H hH.continuous)) := z.property
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hm
  choose f hf using ha
  have hseq : (fun n => smoothGradientGraphLinear hN β H hH.continuous (f n)) = a := funext hf
  rw [← hseq] at hlim
  have ht := ((WithLp.homeomorphProd 2 _ _).continuous.tendsto z.val).comp hlim
  have hu := (continuous_fst.tendsto z.val.ofLp).comp ht
  have hd := (continuous_snd.tendsto z.val.ofLp).comp ht
  change z.val.ofLp.1 = 0 at hz
  rw [hz] at hu
  exact normalizedRotationGradientL2_closable hN β hH (fun n => f n)
    (fun n => (smoothCore_contDiff (f n)).of_le (by simp)) z.val.snd hu hd

/-- The completed Sobolev graph embeds injectively in the actual Gibbs L²
space. Injectivity is a theorem, not a completion-field assumption. -/
theorem sphericalSobolevGraph_injective {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) :
    Function.Injective (fun z : sphericalSobolevGraph hN β H hH.continuous => z.val.fst) := by
  intro u v huv
  have hz : (u - v).val.fst = 0 := by simpa using sub_eq_zero.mpr huv
  have hd := sphericalSobolevGraph_zero_fiber hN β H hH (u - v) hz
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact huv
  · exact sub_eq_zero.mp hd

end
end SlowEquilibration.SphericalForm
