include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "cixp.mm"
include "cvv.mm"
include "wcel.mm"
include "ixpexg.mm"
include "fvexd.mm"
include "mprg.mm"
include "eqeltri.mm"

theorem prdsbasex
  let vx: setvar x
  let cB: class B
  let cR: class R
  assume prdsbasex.b: |- B = X_ x e. dom R ( Base ` ( R ` x ) )

  disjoint R x
  assert |- B e. _V

  proof
    cB
    vx
    cR
    cdm
    #
    vx
    cv
    #
    cR
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    cvv
    prdsbasex.b
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    vx
    @0
    vx
    @0
    @3
    cvv
    ixpexg
    @1
    @0
    wcel
    @2
    cbs
    fvexd
    mprg
    eqeltri
end
