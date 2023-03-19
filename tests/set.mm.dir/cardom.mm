include "com.mm"
include "ccrd.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "omelon.mm"
include "oncardid.mm"
include "ax-mp.mm"
include "csdm.mm"
include "wn.mm"
include "nnsdom.mm"
include "sdomnen.mm"
include "syl.mm"
include "mt2.mm"
include "wss.mm"
include "wo.mm"
include "cardonle.mm"
include "cardon.mm"
include "onsseli.mm"
include "mpbi.mm"
include "mtpor.mm"

theorem cardom



  assert |- ( card ` _om ) = _om

  proof
    com
    ccrd
    cfv
    #
    com
    wcel
    #
    @0
    com
    wceq
    #
    @1
    @0
    com
    cen
    wbr
    #
    com
    con0
    wcel
    #
    @3
    omelon
    com
    oncardid
    ax-mp
    @1
    @0
    com
    csdm
    wbr
    @3
    wn
    @0
    nnsdom
    @0
    com
    sdomnen
    syl
    mt2
    @0
    com
    wss
    #
    @1
    @2
    wo
    @4
    @5
    omelon
    com
    cardonle
    ax-mp
    @0
    com
    com
    cardon
    omelon
    onsseli
    mpbi
    mtpor
end
