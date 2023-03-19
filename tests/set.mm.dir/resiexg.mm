include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "relres.mm"
include "weq.mm"
include "cv.mm"
include "wa.mm"
include "cop.mm"
include "simpr.mm"
include "eleq1.mm"
include "biimpa.mm"
include "jca.mm"
include "vex.mm"
include "opelres.mm"
include "wbr.mm"
include "df-br.mm"
include "ideq.mm"
include "bitr3i.mm"
include "anbi1i.mm"
include "bitri.mm"
include "opelxp.mm"
include "3imtr4i.mm"
include "relssi.mm"
include "sqxpexg.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem resiexg
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( _I |` A ) e. _V )

  proof
    cA
    cV
    wcel
    cid
    cA
    cres
    #
    cA
    cA
    cxp
    #
    wss
    @1
    cvv
    wcel
    @0
    cvv
    wcel
    vx
    vy
    @0
    @1
    cid
    cA
    relres
    vx
    vy
    weq
    #
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @4
    vy
    cv
    #
    cA
    wcel
    #
    wa
    @3
    @6
    cop
    #
    @0
    wcel
    #
    @8
    @1
    wcel
    @5
    @4
    @7
    @2
    @4
    simpr
    @2
    @4
    @7
    @3
    @6
    cA
    eleq1
    biimpa
    jca
    @9
    @8
    cid
    wcel
    #
    @4
    wa
    @5
    @3
    @6
    cid
    cA
    vy
    vex
    #
    opelres
    @10
    @2
    @4
    @10
    @3
    @6
    cid
    wbr
    @2
    @3
    @6
    cid
    df-br
    @3
    @6
    @11
    ideq
    bitr3i
    anbi1i
    bitri
    @3
    @6
    cA
    cA
    opelxp
    3imtr4i
    relssi
    cA
    cV
    sqxpexg
    @0
    @1
    cvv
    ssexg
    sylancr
end
