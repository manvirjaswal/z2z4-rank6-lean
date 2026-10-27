import Z2Z4Rank6.PointScaling

/-! A field-level untwisting embedding with both Weierstrass
models retained. The generic interface keeps coefficient instances and
equation transports fixed before specializing to an extension field. -/

namespace Z2Z4Rank6.FieldTwistEmbedding
noncomputable section
open Common.WeierstrassCoordinates
variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]

def embed (f : F →+* L) (A B d : F) (r : L) (hd : d ≠ 0) (hr : r^2=f d)
    (U : WeierstrassCurve F) (V : WeierstrassCurve L)
    (hU : U=PointScaling.curve (d*A) (d^2*B))
    (hV : PointScaling.curve (f A) (f B)=V) : U.toAffine.Point →+ V.toAffine.Point :=
  (PointScaling.pointCongr hV).toAddMonoidHom.comp
    ((PointScaling.baseChangeUntwistHom f A B d r hd hr).comp
      (PointScaling.pointCongr hU).toAddMonoidHom)

theorem embed_injective (f : F →+* L) (A B d : F) (r : L) (hd : d ≠ 0) (hr : r^2=f d)
    (U : WeierstrassCurve F) (V : WeierstrassCurve L)
    (hU : U=PointScaling.curve (d*A) (d^2*B))
    (hV : PointScaling.curve (f A) (f B)=V) :
    Function.Injective (embed f A B d r hd hr U V hU hV) :=
  (PointScaling.pointCongr hV).injective.comp
    ((PointScaling.baseChangeUntwistHom_injective f A B d r hd hr).comp
      (PointScaling.pointCongr hU).injective)

theorem encode_embed (f : F →+* L) (A B d : F) (r : L) (hd : d ≠ 0) (hr : r^2=f d)
    (U : WeierstrassCurve F) (V : WeierstrassCurve L)
    (hU : U=PointScaling.curve (d*A) (d^2*B))
    (hV : PointScaling.curve (f A) (f B)=V) (P : U.toAffine.Point) :
    encode (embed f A B d r hd hr U V hU hV P)=
      (encode P).map (fun xy=>(f xy.1/f d,f xy.2/(f d*r))) := by
  simp only [embed,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    PointScaling.encode_pointCongr,PointScaling.encode_baseChangeUntwistHom]

structure Data (f : F →+* L) (d : F) (r : L)
    (U : WeierstrassCurve F) (V : WeierstrassCurve L) where
  hom : U.toAffine.Point →+ V.toAffine.Point
  injective : Function.Injective hom
  coordinates (P : U.toAffine.Point) :
    encode (hom P)=(encode P).map (fun xy=>(f xy.1/f d,f xy.2/(f d*r)))

def data (f : F →+* L) (A B d : F) (r : L) (hd : d ≠ 0) (hr : r^2=f d)
    (U : WeierstrassCurve F) (V : WeierstrassCurve L)
    (hU : U=PointScaling.curve (d*A) (d^2*B))
    (hV : PointScaling.curve (f A) (f B)=V) : Data f d r U V :=
  ⟨embed f A B d r hd hr U V hU hV,
    embed_injective f A B d r hd hr U V hU hV,
    encode_embed f A B d r hd hr U V hU hV⟩

theorem Data.hom_unique {f : F →+* L} {d : F} {r : L}
    {U : WeierstrassCurve F} {V : WeierstrassCurve L} (D E : Data f d r U V) :
    D.hom=E.hom := by
  ext P
  apply encode_injective V
  rw [D.coordinates,E.coordinates]

end
end Z2Z4Rank6.FieldTwistEmbedding
