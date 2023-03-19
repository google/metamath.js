include "wcel.mm"
include "cvv.mm"
include "cdif.mm"
include "difexg.mm"
include "wa.mm"
include "cun.mm"
include "wss.mm"
include "ssun2.mm"
include "uncom.mm"
include "undif2.mm"
include "eqtr2i.mm"
include "sseqtri.mm"
include "unexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "expcom.mm"
include "impbid2.mm"

theorem difex2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B e. C -> ( A e. _V <-> ( A \ B ) e. _V ) )

  proof
    cB
    cC
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    cdif
    #
    cvv
    wcel
    #
    cA
    cB
    cvv
    difexg
    @3
    @0
    @1
    @3
    @0
    wa
    cA
    @2
    cB
    cun
    #
    wss
    @4
    cvv
    wcel
    @1
    cA
    cB
    cA
    cun
    #
    @4
    cA
    cB
    ssun2
    @4
    cB
    @2
    cun
    @5
    @2
    cB
    uncom
    cB
    cA
    undif2
    eqtr2i
    sseqtri
    @2
    cB
    cvv
    cC
    unexg
    cA
    @4
    cvv
    ssexg
    sylancr
    expcom
    impbid2
end
