include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cqtop.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "wa.mm"
include "cnvresid.mm"
include "imaeq1i.mm"
include "wceq.mm"
include "resiima.mm"
include "adantl.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "pm5.32da.mm"
include "wfo.mm"
include "wb.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1ofo.mm"
include "mp1i.mm"
include "elqtop3.mm"
include "mpdan.mm"
include "toponss.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem idqtop
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cY: class Y


  assert |- ( J e. ( TopOn ` X ) -> ( J qTop ( _I |` X ) ) = J )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    vx
    cJ
    cid
    cX
    cres
    #
    cqtop
    co
    #
    cJ
    @0
    vx
    cv
    #
    cX
    wss
    #
    @1
    ccnv
    #
    @3
    cima
    #
    cJ
    wcel
    #
    wa
    #
    @4
    @3
    cJ
    wcel
    #
    wa
    @3
    @2
    wcel
    #
    @9
    @0
    @4
    @7
    @9
    @0
    @4
    wa
    #
    @6
    @3
    cJ
    @11
    @6
    @1
    @3
    cima
    #
    @3
    @5
    @1
    @3
    cX
    cnvresid
    imaeq1i
    @4
    @12
    @3
    wceq
    @0
    cX
    @3
    resiima
    adantl
    syl5eq
    eleq1d
    pm5.32da
    @0
    cX
    cX
    @1
    wfo
    #
    @10
    @8
    wb
    cX
    cX
    @1
    wf1o
    @13
    @0
    cX
    f1oi
    cX
    cX
    @1
    f1ofo
    mp1i
    @3
    @1
    cJ
    cX
    cX
    elqtop3
    mpdan
    @0
    @9
    @4
    @0
    @9
    @4
    @3
    cJ
    cX
    toponss
    ex
    pm4.71rd
    3bitr4d
    eqrdv
end
