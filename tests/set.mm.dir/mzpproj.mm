include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "cmzpcl.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "mzpincl.mm"
include "mzpcl2.mm"
include "sylan.mm"

theorem mzpproj
  let vg: setvar g
  let cV: class V
  let cX: class X

  disjoint X g
  disjoint V g
  assert |- ( ( V e. _V /\ X e. V ) -> ( g e. ( ZZ ^m V ) |-> ( g ` X ) ) e. ( mzPoly ` V ) )

  proof
    cV
    cvv
    wcel
    cV
    cmzp
    cfv
    #
    cV
    cmzpcl
    cfv
    wcel
    cX
    cV
    wcel
    vg
    cz
    cV
    cmap
    co
    cX
    vg
    cv
    cfv
    cmpt
    @0
    wcel
    cV
    mzpincl
    @0
    vg
    cX
    cV
    mzpcl2
    sylan
end
