include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "cnvss.mm"
include "cnvco.mm"
include "cnveqi.mm"
include "cocnvcnv1.mm"
include "cocnvcnv2.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "sseq1i.mm"
include "biimpi.mm"
include "cnvcnvss.mm"
include "syl6ss.mm"
include "syl.mm"
include "impbii.mm"
include "bitri.mm"

theorem cnvtrrel
  let cS: class S


  assert |- ( ( S o. S ) C_ S <-> ( `' S o. `' S ) C_ `' S )

  proof
    cS
    cS
    ccom
    #
    cS
    wss
    #
    @0
    ccnv
    #
    cS
    ccnv
    #
    wss
    #
    @3
    @3
    ccom
    #
    @3
    wss
    @1
    @4
    @0
    cS
    cnvss
    @4
    @2
    ccnv
    #
    @3
    ccnv
    #
    wss
    #
    @1
    @2
    @3
    cnvss
    @8
    @0
    @7
    cS
    @8
    @0
    @7
    wss
    @6
    @0
    @7
    @6
    @5
    ccnv
    @7
    @7
    ccom
    #
    @0
    @2
    @5
    cS
    cS
    cnvco
    #
    cnveqi
    @3
    @3
    cnvco
    @9
    cS
    @7
    ccom
    @0
    cS
    @7
    cocnvcnv1
    cS
    cS
    cocnvcnv2
    eqtri
    3eqtri
    sseq1i
    biimpi
    cS
    cnvcnvss
    syl6ss
    syl
    impbii
    @2
    @5
    @3
    @10
    sseq1i
    bitri
end
