include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "con0.mm"
include "isfi.mm"
include "wa.mm"
include "wceq.mm"
include "onomeneq.mm"
include "wi.mm"
include "eleq1a.mm"
include "adantl.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "enrefg.mm"
include "breq2.mm"
include "rspcev.mm"
include "mpdan.mm"
include "impbid1.mm"
include "syl5bb.mm"

theorem onfin
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( A e. Fin <-> A e. _om ) )

  proof
    cA
    cfn
    wcel
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    #
    cA
    con0
    wcel
    #
    cA
    com
    wcel
    #
    vx
    cA
    isfi
    @3
    @2
    @4
    @3
    @1
    @4
    vx
    com
    @3
    @0
    com
    wcel
    #
    wa
    @1
    cA
    @0
    wceq
    #
    @4
    cA
    @0
    onomeneq
    @5
    @6
    @4
    wi
    @3
    @0
    com
    cA
    eleq1a
    adantl
    sylbid
    rexlimdva
    @4
    cA
    cA
    cen
    wbr
    #
    @2
    cA
    com
    enrefg
    @1
    @7
    vx
    cA
    com
    @0
    cA
    cA
    cen
    breq2
    rspcev
    mpdan
    impbid1
    syl5bb
end
