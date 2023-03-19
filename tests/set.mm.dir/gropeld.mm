include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wsbc.mm"
include "gropd.mm"
include "sbcel1v.mm"
include "sylib.mm"

theorem gropeld
  let wph: wff ph
  let cC: class C
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cV: class V
  let cW: class W
  assume gropeld.g: |- ( ph -> A. g ( ( ( Vtx ` g ) = V /\ ( iEdg ` g ) = E ) -> g e. C ) )
  assume gropeld.v: |- ( ph -> V e. U )
  assume gropeld.e: |- ( ph -> E e. W )

  disjoint C g
  disjoint E g
  disjoint V g
  disjoint g ph
  assert |- ( ph -> <. V , E >. e. C )

  proof
    wph
    vg
    cv
    cC
    wcel
    #
    vg
    cV
    cE
    cop
    #
    wsbc
    @1
    cC
    wcel
    wph
    @0
    cU
    vg
    cE
    cV
    cW
    gropeld.g
    gropeld.v
    gropeld.e
    gropd
    vg
    @1
    cC
    sbcel1v
    sylib
end
