include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnv.mm"
include "cnvexg.mm"
include "wceq.mm"
include "wi.mm"
include "dfrel2.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "sylbi.mm"
include "impbid2.mm"

theorem relcnvexb
  let cR: class R


  assert |- ( Rel R -> ( R e. _V <-> `' R e. _V ) )

  proof
    cR
    wrel
    #
    cR
    cvv
    wcel
    #
    cR
    ccnv
    #
    cvv
    wcel
    #
    cR
    cvv
    cnvexg
    @0
    @2
    ccnv
    #
    cR
    wceq
    #
    @3
    @1
    wi
    cR
    dfrel2
    @3
    @4
    cvv
    wcel
    @5
    @1
    @2
    cvv
    cnvexg
    @4
    cR
    cvv
    eleq1
    syl5ib
    sylbi
    impbid2
end
