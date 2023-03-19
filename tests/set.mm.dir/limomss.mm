include "word.mm"
include "wlim.mm"
include "com.mm"
include "wss.mm"
include "limord.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "ordeleqon.mm"
include "wa.mm"
include "cv.mm"
include "wal.mm"
include "elom.mm"
include "simprbi.mm"
include "limeq.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl5.mm"
include "com23.mm"
include "imp.mm"
include "ssrdv.mm"
include "ex.mm"
include "omsson.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "a1d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "mpcom.mm"

theorem limomss
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( Lim A -> _om C_ A )

  proof
    cA
    word
    #
    cA
    wlim
    #
    com
    cA
    wss
    #
    cA
    limord
    @0
    cA
    con0
    wcel
    #
    cA
    con0
    wceq
    #
    wo
    @1
    @2
    wi
    #
    cA
    ordeleqon
    @3
    @5
    @4
    @3
    @1
    @2
    @3
    @1
    wa
    vx
    com
    cA
    @3
    @1
    vx
    cv
    #
    com
    wcel
    #
    @6
    cA
    wcel
    #
    wi
    @3
    @7
    @1
    @8
    @7
    vy
    cv
    #
    wlim
    #
    @6
    @9
    wcel
    #
    wi
    #
    vy
    wal
    #
    @3
    @1
    @8
    wi
    #
    @7
    @6
    con0
    wcel
    @13
    vy
    @6
    elom
    simprbi
    @12
    @14
    vy
    cA
    con0
    @9
    cA
    wceq
    @10
    @1
    @11
    @8
    @9
    cA
    limeq
    @9
    cA
    @6
    eleq2
    imbi12d
    spcgv
    syl5
    com23
    imp
    ssrdv
    ex
    @4
    @2
    @1
    @4
    @2
    com
    con0
    wss
    omsson
    cA
    con0
    com
    sseq2
    mpbiri
    a1d
    jaoi
    sylbi
    mpcom
end
