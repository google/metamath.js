include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "wpss.mm"
include "sucidg.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "ordsuc.mm"
include "sylib.mm"
include "ordelpss.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem onpsssuc
  let cA: class A


  assert |- ( A e. On -> A C. suc A )

  proof
    cA
    con0
    wcel
    #
    cA
    cA
    csuc
    #
    wcel
    #
    cA
    @1
    wpss
    #
    cA
    con0
    sucidg
    @0
    cA
    word
    #
    @1
    word
    #
    @2
    @3
    wb
    cA
    eloni
    #
    @0
    @4
    @5
    @6
    cA
    ordsuc
    sylib
    cA
    @1
    ordelpss
    syl2anc
    mpbid
end
