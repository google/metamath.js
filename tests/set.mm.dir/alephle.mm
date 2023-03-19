include "cv.mm"
include "cale.mm"
include "cfv.mm"
include "wss.mm"
include "weq.mm"
include "id.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "wceq.mm"
include "con0.mm"
include "wcel.mm"
include "wral.mm"
include "wel.mm"
include "wa.mm"
include "alephord2i.mm"
include "imp.mm"
include "wi.mm"
include "onelon.mm"
include "alephon.mm"
include "ontr2.mm"
include "sylancl.mm"
include "mpan2d.mm"
include "ralimdva.mm"
include "wn.mm"
include "onirri.mm"
include "eleq1.mm"
include "rspccv.mm"
include "mtoi.mm"
include "wb.mm"
include "ontri1.mm"
include "mpan2.mm"
include "syl5ibr.mm"
include "syld.mm"
include "tfis3.mm"

theorem alephle
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> A C_ ( aleph ` A ) )

  proof
    vx
    cv
    #
    @0
    cale
    cfv
    #
    wss
    #
    vy
    cv
    #
    @3
    cale
    cfv
    #
    wss
    #
    cA
    cA
    cale
    cfv
    #
    wss
    vx
    vy
    cA
    vx
    vy
    weq
    #
    @0
    @3
    @1
    @4
    @7
    id
    @0
    @3
    cale
    fveq2
    sseq12d
    @0
    cA
    wceq
    #
    @0
    cA
    @1
    @6
    @8
    id
    @0
    cA
    cale
    fveq2
    sseq12d
    @0
    con0
    wcel
    #
    @5
    vy
    @0
    wral
    @3
    @1
    wcel
    #
    vy
    @0
    wral
    #
    @2
    @9
    @5
    @10
    vy
    @0
    @9
    vy
    vx
    wel
    #
    wa
    #
    @5
    @4
    @1
    wcel
    #
    @10
    @9
    @12
    @14
    @3
    @0
    alephord2i
    imp
    @13
    @3
    con0
    wcel
    @1
    con0
    wcel
    #
    @5
    @14
    wa
    @10
    wi
    @0
    @3
    onelon
    @0
    alephon
    #
    @3
    @4
    @1
    ontr2
    sylancl
    mpan2d
    ralimdva
    @11
    @2
    @9
    @1
    @0
    wcel
    #
    wn
    #
    @11
    @17
    @1
    @1
    wcel
    #
    @1
    @16
    onirri
    @10
    @19
    vy
    @1
    @0
    @3
    @1
    @1
    eleq1
    rspccv
    mtoi
    @9
    @15
    @2
    @18
    wb
    @16
    @0
    @1
    ontri1
    mpan2
    syl5ibr
    syld
    tfis3
end
