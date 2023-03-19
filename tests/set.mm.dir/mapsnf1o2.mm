include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "cv.mm"
include "cfv.mm"
include "fvex.mm"
include "fnmpti.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "snex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mapsncnv.mm"
include "dff1o4.mm"
include "mpbir2an.mm"

theorem mapsnf1o2
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cF: class F
  let cX: class X
  let vy: setvar y
  assume mapsncnv.s: |- S = { X }
  assume mapsncnv.b: |- B e. _V
  assume mapsncnv.x: |- X e. _V
  assume mapsncnv.f: |- F = ( x e. ( B ^m S ) |-> ( x ` X ) )

  disjoint B x
  disjoint S x
  disjoint B y
  disjoint x y
  disjoint S y
  disjoint X y
  assert |- F : ( B ^m S ) -1-1-onto-> B

  proof
    cB
    cS
    cmap
    co
    #
    cB
    cF
    wf1o
    cF
    @0
    wfn
    cF
    ccnv
    #
    cB
    wfn
    vx
    @0
    cX
    vx
    cv
    #
    cfv
    cF
    cX
    @2
    fvex
    mapsncnv.f
    fnmpti
    vy
    cB
    cS
    vy
    cv
    #
    csn
    #
    cxp
    @1
    cS
    @4
    cS
    cX
    csn
    cvv
    mapsncnv.s
    cX
    snex
    eqeltri
    @3
    snex
    xpex
    vx
    vy
    cB
    cS
    cF
    cX
    mapsncnv.s
    mapsncnv.b
    mapsncnv.x
    mapsncnv.f
    mapsncnv
    fnmpti
    @0
    cB
    cF
    dff1o4
    mpbir2an
end
