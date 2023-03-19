include "cvv.mm"
include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "df-nel.mm"
include "word.mm"
include "wo.mm"
include "ssorduni.mm"
include "ordeleqon.mm"
include "sylib.mm"
include "orcomd.mm"
include "ord.mm"
include "uniexr.mm"
include "syl6.mm"
include "con1d.mm"
include "onprc.mm"
include "uniexg.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "mtoi.mm"
include "impbid1.mm"
include "syl5bb.mm"

theorem ssonprc
  let cA: class A


  assert |- ( A C_ On -> ( A e/ _V <-> U. A = On ) )

  proof
    cA
    cvv
    wnel
    cA
    cvv
    wcel
    #
    wn
    #
    cA
    con0
    wss
    #
    cA
    cuni
    #
    con0
    wceq
    #
    cA
    cvv
    df-nel
    @2
    @1
    @4
    @2
    @4
    @0
    @2
    @4
    wn
    @3
    con0
    wcel
    #
    @0
    @2
    @4
    @5
    @2
    @5
    @4
    @2
    @3
    word
    @5
    @4
    wo
    cA
    ssorduni
    @3
    ordeleqon
    sylib
    orcomd
    ord
    cA
    con0
    uniexr
    syl6
    con1d
    @4
    @0
    con0
    cvv
    wcel
    #
    onprc
    @0
    @3
    cvv
    wcel
    @4
    @6
    cA
    cvv
    uniexg
    @3
    con0
    cvv
    eleq1
    syl5ib
    mtoi
    impbid1
    syl5bb
end
