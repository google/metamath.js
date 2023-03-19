include "cfin6.mm"
include "wcel.mm"
include "cv.mm"
include "c2o.mm"
include "csdm.mm"
include "wbr.mm"
include "cxp.mm"
include "wo.mm"
include "cab.mm"
include "df-fin6.mm"
include "eleq2i.mm"
include "cvv.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "jaoi.mm"
include "wceq.mm"
include "breq1.mm"
include "id.mm"
include "sqxpeqd.mm"
include "breq12d.mm"
include "orbi12d.mm"
include "elab3.mm"
include "bitri.mm"

theorem isfin6
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cX: class X


  assert |- ( A e. Fin6 <-> ( A ~< 2o \/ A ~< ( A X. A ) ) )

  proof
    cA
    cfin6
    wcel
    cA
    vx
    cv
    #
    c2o
    csdm
    wbr
    #
    @0
    @0
    @0
    cxp
    #
    csdm
    wbr
    #
    wo
    #
    vx
    cab
    #
    wcel
    cA
    c2o
    csdm
    wbr
    #
    cA
    cA
    cA
    cxp
    #
    csdm
    wbr
    #
    wo
    #
    cfin6
    @5
    cA
    vx
    df-fin6
    eleq2i
    @4
    @9
    vx
    cA
    @6
    cA
    cvv
    wcel
    @8
    cA
    c2o
    csdm
    relsdom
    brrelexi
    cA
    @7
    csdm
    relsdom
    brrelexi
    jaoi
    @0
    cA
    wceq
    #
    @1
    @6
    @3
    @8
    @0
    cA
    c2o
    csdm
    breq1
    @10
    @0
    cA
    @2
    @7
    csdm
    @10
    id
    #
    @10
    @0
    cA
    @11
    sqxpeqd
    breq12d
    orbi12d
    elab3
    bitri
end
