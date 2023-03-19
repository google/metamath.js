include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "eqid.mm"
include "mapsnf1o2.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "csn.mm"
include "cxp.mm"
include "mapsncnv.mm"
include "eqtr4i.mm"
include "f1oeq1.mm"
include "mpbir.mm"

theorem mapsnf1o3
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cF: class F
  let cX: class X
  let vx: setvar x
  assume mapsncnv.s: |- S = { X }
  assume mapsncnv.b: |- B e. _V
  assume mapsncnv.x: |- X e. _V
  assume mapsnf1o3.f: |- F = ( y e. B |-> ( S X. { y } ) )

  disjoint B y
  disjoint S y
  disjoint X y
  disjoint B x
  disjoint x y
  disjoint S x
  assert |- F : B -1-1-onto-> ( B ^m S )

  proof
    cB
    cB
    cS
    cmap
    co
    #
    cF
    wf1o
    #
    cB
    @0
    vx
    @0
    cX
    vx
    cv
    cfv
    cmpt
    #
    ccnv
    #
    wf1o
    #
    @0
    cB
    @2
    wf1o
    @4
    vx
    cB
    cS
    @2
    cX
    mapsncnv.s
    mapsncnv.b
    mapsncnv.x
    @2
    eqid
    #
    mapsnf1o2
    @0
    cB
    @2
    f1ocnv
    ax-mp
    cF
    @3
    wceq
    @1
    @4
    wb
    cF
    vy
    cB
    cS
    vy
    cv
    csn
    cxp
    cmpt
    @3
    mapsnf1o3.f
    vx
    vy
    cB
    cS
    @2
    cX
    mapsncnv.s
    mapsncnv.b
    mapsncnv.x
    @5
    mapsncnv
    eqtr4i
    cB
    @0
    cF
    @3
    f1oeq1
    ax-mp
    mpbir
end
