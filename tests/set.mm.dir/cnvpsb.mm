include "wrel.mm"
include "cps.mm"
include "wcel.mm"
include "ccnv.mm"
include "cnvps.mm"
include "wceq.mm"
include "wi.mm"
include "dfrel2.mm"
include "eleq1.mm"
include "biimpd.mm"
include "sylbi.mm"
include "syl5.mm"
include "impbid2.mm"

theorem cnvpsb
  let cR: class R


  assert |- ( Rel R -> ( R e. PosetRel <-> `' R e. PosetRel ) )

  proof
    cR
    wrel
    #
    cR
    cps
    wcel
    #
    cR
    ccnv
    #
    cps
    wcel
    #
    cR
    cnvps
    @3
    @2
    ccnv
    #
    cps
    wcel
    #
    @0
    @1
    @2
    cnvps
    @0
    @4
    cR
    wceq
    #
    @5
    @1
    wi
    cR
    dfrel2
    @6
    @5
    @1
    @4
    cR
    cps
    eleq1
    biimpd
    sylbi
    syl5
    impbid2
end
