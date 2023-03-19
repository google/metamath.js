include "con0.mm"
include "wss.mm"
include "cint.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cvv.mm"
include "0ex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "intex.mm"
include "sylibr.mm"
include "onint.mm"
include "sylan2.mm"
include "wb.mm"
include "adantl.mm"
include "mpbid.mm"
include "ex.mm"
include "int0el.mm"
include "impbid1.mm"

theorem onint0
  let cA: class A


  assert |- ( A C_ On -> ( |^| A = (/) <-> (/) e. A ) )

  proof
    cA
    con0
    wss
    #
    cA
    cint
    #
    c0
    wceq
    #
    c0
    cA
    wcel
    #
    @0
    @2
    @3
    @0
    @2
    wa
    @1
    cA
    wcel
    #
    @3
    @2
    @0
    cA
    c0
    wne
    #
    @4
    @2
    @1
    cvv
    wcel
    #
    @5
    @2
    @6
    c0
    cvv
    wcel
    0ex
    @1
    c0
    cvv
    eleq1
    mpbiri
    cA
    intex
    sylibr
    cA
    onint
    sylan2
    @2
    @4
    @3
    wb
    @0
    @1
    c0
    cA
    eleq1
    adantl
    mpbid
    ex
    cA
    int0el
    impbid1
end
