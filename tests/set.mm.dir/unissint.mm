include "cuni.mm"
include "cint.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "simpl.mm"
include "wne.mm"
include "df-ne.mm"
include "intssuni.mm"
include "sylbir.mm"
include "adantl.mm"
include "eqssd.mm"
include "ex.mm"
include "orrd.mm"
include "cvv.mm"
include "ssv.mm"
include "int0.mm"
include "sseqtr4i.mm"
include "inteq.mm"
include "syl5sseqr.mm"
include "eqimss.mm"
include "jaoi.mm"
include "impbii.mm"

theorem unissint
  let cA: class A


  assert |- ( U. A C_ |^| A <-> ( A = (/) \/ U. A = |^| A ) )

  proof
    cA
    cuni
    #
    cA
    cint
    #
    wss
    #
    cA
    c0
    wceq
    #
    @0
    @1
    wceq
    #
    wo
    @2
    @3
    @4
    @2
    @3
    wn
    #
    @4
    @2
    @5
    wa
    @0
    @1
    @2
    @5
    simpl
    @5
    @1
    @0
    wss
    #
    @2
    @5
    cA
    c0
    wne
    @6
    cA
    c0
    df-ne
    cA
    intssuni
    sylbir
    adantl
    eqssd
    ex
    orrd
    @3
    @2
    @4
    @3
    c0
    cint
    #
    @0
    @1
    @0
    cvv
    @7
    @0
    ssv
    int0
    sseqtr4i
    cA
    c0
    inteq
    syl5sseqr
    @0
    @1
    eqimss
    jaoi
    impbii
end
