module
public import QuantitativeFollowup.ChenScalarConvexity
public import QuantitativeFollowup.ChenSmoothDatum

@[expose] public section

/-! Repeated genuine scalar Gaussian smoothing. Each coordinate step preserves
joint convexity on both signed parameter half-planes and all the smoothness
needed for the next coordinate step. -/
noncomputable section
open Set
open scoped Topology NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper ColeHopfFoundation.ProbabilityTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def gaussianCoordinateLift (v : E) (F : ℝ × E → ℝ) (p : ℝ × E × ℝ) : ℝ :=
  F (p.1,p.2.1+p.2.2 • v)

def gaussianCoordinateStep (v : E) (F : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  coleHopf p.1 1 (fun y=>F (p.1,p.2+y • v)) 0

def iteratedScalarGaussian : List E → (ℝ × E → ℝ) → ℝ × E → ℝ
  | [],F=>F
  | v::vs,F=>gaussianCoordinateStep v (iteratedScalarGaussian vs F)

theorem convexOn_gaussianCoordinateLift {S : Set ℝ} (hS : Convex ℝ S)
    (v : E) (F : ℝ × E → ℝ) (hF : ConvexOn ℝ (S ×ˢ (univ : Set E)) F) :
    ConvexOn ℝ (S ×ˢ (univ : Set (E × ℝ))) (gaussianCoordinateLift v F) := by
  refine ⟨hS.prod convex_univ,?_⟩
  rintro ⟨m0,z0,y0⟩ hp0 ⟨m1,z1,y1⟩ hp1 a b ha hb hab
  have hh := hF.2 (show (m0,z0+y0 • v) ∈ S ×ˢ (univ : Set E) from ⟨hp0.1,mem_univ _⟩)
    (show (m1,z1+y1 • v) ∈ S ×ˢ (univ : Set E) from ⟨hp1.1,mem_univ _⟩) ha hb hab
  have he : (a • z0+b • z1)+(a*y0+b*y1) • v=
      a • (z0+y0 • v)+b • (z1+y1 • v) := by module
  change F (a*m0+b*m1,(a • z0+b • z1)+(a*y0+b*y1) • v) ≤ _
  rw [he]
  exact hh

theorem convexOn_gaussianCoordinateStep_positive (v : E) (F : ℝ × E → ℝ)
    (hF : ConvexOn ℝ ((Ioi (0:ℝ)) ×ˢ (univ : Set E)) F)
    (hreg : ∀ m,BoundedPositiveJets (fun x=>F (m,x))) :
    ConvexOn ℝ ((Ioi (0:ℝ)) ×ˢ (univ : Set E)) (gaussianCoordinateStep v F) := by
  exact convexOn_signedGaussianStep_positive (gaussianCoordinateLift v F)
    (convexOn_gaussianCoordinateLift (convex_Ioi 0) v F hF)
    (fun m x=>signedScalarDatum_line (hreg m) x v)

theorem convexOn_gaussianCoordinateStep_negative (v : E) (F : ℝ × E → ℝ)
    (hF : ConvexOn ℝ ((Iio (0:ℝ)) ×ˢ (univ : Set E)) F)
    (hreg : ∀ m,BoundedPositiveJets (fun x=>F (m,x))) :
    ConvexOn ℝ ((Iio (0:ℝ)) ×ˢ (univ : Set E)) (gaussianCoordinateStep v F) := by
  exact convexOn_signedGaussianStep_negative (gaussianCoordinateLift v F)
    (convexOn_gaussianCoordinateLift (convex_Iio 0) v F hF)
    (fun m x=>signedScalarDatum_line (hreg m) x v)

theorem boundedPositiveJets_iteratedScalarGaussian (vs : List E) (F : ℝ × E → ℝ)
    (hF : ∀ m,BoundedPositiveJets (fun x=>F (m,x))) :
    ∀ m,BoundedPositiveJets (fun x=>iteratedScalarGaussian vs F (m,x)) := by
  induction vs with
  | nil => exact hF
  | cons v vs ih =>
    intro m
    exact boundedPositiveJets_scalarColeHopf (ih m) v m

theorem convexOn_iteratedScalarGaussian_positive (vs : List E) (F : ℝ × E → ℝ)
    (hF : ConvexOn ℝ ((Ioi (0:ℝ)) ×ˢ (univ : Set E)) F)
    (hreg : ∀ m,BoundedPositiveJets (fun x=>F (m,x))) :
    ConvexOn ℝ ((Ioi (0:ℝ)) ×ˢ (univ : Set E)) (iteratedScalarGaussian vs F) := by
  induction vs with
  | nil => exact hF
  | cons v vs ih =>
    exact convexOn_gaussianCoordinateStep_positive v _ ih
      (boundedPositiveJets_iteratedScalarGaussian vs F hreg)

theorem convexOn_iteratedScalarGaussian_negative (vs : List E) (F : ℝ × E → ℝ)
    (hF : ConvexOn ℝ ((Iio (0:ℝ)) ×ˢ (univ : Set E)) F)
    (hreg : ∀ m,BoundedPositiveJets (fun x=>F (m,x))) :
    ConvexOn ℝ ((Iio (0:ℝ)) ×ˢ (univ : Set E)) (iteratedScalarGaussian vs F) := by
  induction vs with
  | nil => exact hF
  | cons v vs ih =>
    exact convexOn_gaussianCoordinateStep_negative v _ ih
      (boundedPositiveJets_iteratedScalarGaussian vs F hreg)

end QuantitativeFollowup
