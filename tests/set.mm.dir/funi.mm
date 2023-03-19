include "cid.mm"
include "wfun.mm"
include "wrel.mm"
include "ccnv.mm"
include "ccom.mm"
include "wss.mm"
include "reli.mm"
include "wceq.mm"
include "relcnv.mm"
include "coi2.mm"
include "ax-mp.mm"
include "cnvi.mm"
include "eqtri.mm"
include "eqimssi.mm"
include "df-fun.mm"
include "mpbir2an.mm"

theorem funi



  assert |- Fun _I

  proof
    cid
    wfun
    cid
    wrel
    cid
    cid
    ccnv
    #
    ccom
    #
    cid
    wss
    reli
    @1
    cid
    @1
    @0
    cid
    @0
    wrel
    @1
    @0
    wceq
    cid
    relcnv
    @0
    coi2
    ax-mp
    cnvi
    eqtri
    eqimssi
    cid
    df-fun
    mpbir2an
end
