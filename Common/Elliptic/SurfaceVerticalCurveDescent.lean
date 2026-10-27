module

public import Common.Elliptic.SurfaceVerticalCurves
public import Common.Elliptic.SurfaceBaseChangeGenericFiber
public import Common.AlgebraicGeometry.ConstantMapDescent

@[expose] public section

/-! Verticality of closed curves descends along constant extension. -/
namespace Common.Elliptic.SurfaceBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits SurfaceModel
open Common.AlgebraicGeometry Common.AlgebraicGeometry.ClosedSubschemeDescent
open Common.AlgebraicGeometry.K3BaseChange Common.AlgebraicGeometry.ConstantMapDescent
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K] [IsAlgClosed k]
  {W : WeierstrassCurve (RatFunc k)} (M : RegularModel k W)
  (hr : IsRegularScheme (scheme k K M)) (hd : topologicalKrullDim (scheme k K M)=2)

theorem verticalCurve_descends (E : VerticalCurve K (model k K M hr hd))
    (C : ClosedCurve M.scheme)
    (hCE : C.toClosedSubscheme.IsBaseChange E.toClosedSubscheme (coefficientMap k K M)) :
    ∃ E0 : VerticalCurve k M,E0.toClosedCurve=C := by
  let := C.closed
  let := C.integral
  let : IsProper M.structureMap := by dsimp [RegularModel.structureMap]; infer_instance
  let : IsProper (C.structureMap M.structureMap) := by
    dsimp [ClosedSubscheme.structureMap]
    infer_instance
  obtain ⟨a,ha⟩ := point_exists k C.scheme (C.structureMap M.structureMap)
  obtain ⟨q,hq⟩ := hCE
  have hfield : IsPullback q E.structureMap (C.structureMap M.structureMap) (extensionMap k K) :=
    hq.paste_vert (structure_isPullback k K M)
  have hc : q≫(C.immersion≫M.projection)=
      E.structureMap≫(E.point≫ProjectiveLine.coefficientMap k K) := by
    calc
      _=(q≫C.immersion)≫M.projection := (Category.assoc _ _ _).symm
      _=E.immersion≫coefficientMap k K M≫M.projection := by rw [hq.w,Category.assoc]
      _=E.immersion≫projection k K M≫ProjectiveLine.coefficientMap k K := by
        rw [show coefficientMap k K M≫M.projection=
          projection k K M≫ProjectiveLine.coefficientMap k K from pullback.condition]
      _=(E.immersion≫(model k K M hr hd).projection)≫ProjectiveLine.coefficientMap k K :=
        (Category.assoc _ _ _).symm
      _=_ := by rw [E.vertical]; rfl
  have hv := constant_descends_of_point k K hfield a ha (C.immersion≫M.projection)
    (E.point≫ProjectiveLine.coefficientMap k K) hc
  refine ⟨{
    toClosedCurve := C
    point := a≫C.immersion≫M.projection
    point_over := ?_
    vertical := hv
  },rfl⟩
  simpa [ClosedSubscheme.structureMap,RegularModel.structureMap,Category.assoc] using ha

end
end Common.Elliptic.SurfaceBaseChange
