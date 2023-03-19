include "wrel.mm"
include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "cnvco.mm"
include "cnvss.mm"
include "syl5eqssr.mm"
include "wceq.mm"
include "wi.mm"
include "sseq1.mm"
include "dfrel2.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqtrd.mm"
include "id.mm"
include "sseq12d.mm"
include "biimpd.mm"
include "sylbi.mm"
include "com12.mm"
include "syl6bi.mm"
include "mpsyl.mm"
include "impbid2.mm"

theorem relcnvtr
  let cR: class R


  assert |- ( Rel R -> ( ( R o. R ) C_ R <-> ( `' R o. `' R ) C_ `' R ) )

  proof
    cR
    wrel
    #
    cR
    cR
    ccom
    #
    cR
    wss
    #
    cR
    ccnv
    #
    @3
    ccom
    #
    @3
    wss
    #
    @2
    @4
    @1
    ccnv
    @3
    cR
    cR
    cnvco
    @1
    cR
    cnvss
    syl5eqssr
    @5
    @0
    @2
    @4
    ccnv
    #
    @3
    ccnv
    #
    @7
    ccom
    #
    wceq
    #
    @5
    @6
    @7
    wss
    #
    @0
    @2
    wi
    #
    @3
    @3
    cnvco
    @4
    @3
    cnvss
    @9
    @10
    @8
    @7
    wss
    #
    @11
    @6
    @8
    @7
    sseq1
    @0
    @12
    @2
    @0
    @7
    cR
    wceq
    #
    @12
    @2
    wi
    cR
    dfrel2
    @13
    @12
    @2
    @13
    @8
    @1
    @7
    cR
    @13
    @8
    cR
    @7
    ccom
    @1
    @7
    cR
    @7
    coeq1
    @7
    cR
    cR
    coeq2
    eqtrd
    @13
    id
    sseq12d
    biimpd
    sylbi
    com12
    syl6bi
    mpsyl
    com12
    impbid2
end
