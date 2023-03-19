include "wrel.mm"
include "ccnv.mm"
include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "hmeocnv.mm"
include "wceq.mm"
include "wb.mm"
include "dfrel2.mm"
include "eleq1.mm"
include "sylbi.mm"
include "syl5ib.mm"
include "impbid1.mm"

theorem hmeocnvb
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( Rel F -> ( `' F e. ( J Homeo K ) <-> F e. ( K Homeo J ) ) )

  proof
    cF
    wrel
    #
    cF
    ccnv
    #
    cJ
    cK
    chmeo
    co
    wcel
    #
    cF
    cK
    cJ
    chmeo
    co
    #
    wcel
    #
    @2
    @1
    ccnv
    #
    @3
    wcel
    #
    @0
    @4
    @1
    cJ
    cK
    hmeocnv
    @0
    @5
    cF
    wceq
    @6
    @4
    wb
    cF
    dfrel2
    @5
    cF
    @3
    eleq1
    sylbi
    syl5ib
    cF
    cK
    cJ
    hmeocnv
    impbid1
end
