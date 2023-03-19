include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "grstructd.mm"
include "sbcel1v.mm"
include "sylib.mm"

theorem grstructeld
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  assume gropeld.g: |- ( ph -> A. g ( ( ( Vtx ` g ) = V /\ ( iEdg ` g ) = E ) -> g e. C ) )
  assume gropeld.v: |- ( ph -> V e. U )
  assume gropeld.e: |- ( ph -> E e. W )
  assume grstructeld.s: |- ( ph -> S e. X )
  assume grstructeld.f: |- ( ph -> Fun ( S \ { (/) } ) )
  assume grstructeld.d: |- ( ph -> 2 <_ ( # ` dom S ) )
  assume grstructeld.b: |- ( ph -> ( Base ` S ) = V )
  assume grstructeld.e: |- ( ph -> ( .ef ` S ) = E )

  disjoint C g
  disjoint E g
  disjoint V g
  disjoint g ph
  disjoint S g
  assert |- ( ph -> S e. C )

  proof
    wph
    vg
    cv
    cC
    wcel
    #
    vg
    cS
    wsbc
    cS
    cC
    wcel
    wph
    @0
    cS
    cU
    vg
    cE
    cV
    cW
    cX
    gropeld.g
    gropeld.v
    gropeld.e
    grstructeld.s
    grstructeld.f
    grstructeld.d
    grstructeld.b
    grstructeld.e
    grstructd
    vg
    cS
    cC
    sbcel1v
    sylib
end
