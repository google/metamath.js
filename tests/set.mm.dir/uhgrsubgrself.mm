include "cuhgr.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "wa.mm"
include "ssid.mm"
include "pm3.2i.mm"
include "wfun.mm"
include "wb.mm"
include "eqid.mm"
include "uhgrfun.mm"
include "id.mm"
include "uhgrissubgr.mm"
include "mpd3an23.mm"
include "mpbiri.mm"

theorem uhgrsubgrself
  let cG: class G


  assert |- ( G e. UHGraph -> G SubGraph G )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    cG
    csubgr
    wbr
    #
    cG
    cvtx
    cfv
    #
    @2
    wss
    #
    cG
    ciedg
    cfv
    #
    @4
    wss
    #
    wa
    #
    @3
    @5
    @2
    ssid
    @4
    ssid
    pm3.2i
    @0
    @4
    wfun
    @0
    @1
    @6
    wb
    @4
    cG
    @4
    eqid
    #
    uhgrfun
    @0
    id
    @2
    @4
    cG
    cG
    @4
    @2
    cuhgr
    @2
    eqid
    #
    @8
    @7
    @7
    uhgrissubgr
    mpd3an23
    mpbiri
end
