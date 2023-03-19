include "com.mm"
include "ccf.mm"
include "cfv.mm"
include "cfle.mm"
include "wlim.mm"
include "wss.mm"
include "limom.mm"
include "omex.mm"
include "cflim2.mm"
include "mpbi.mm"
include "limomss.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem cfom



  assert |- ( cf ` _om ) = _om

  proof
    com
    ccf
    cfv
    #
    com
    com
    cfle
    @0
    wlim
    #
    com
    @0
    wss
    com
    wlim
    @1
    limom
    com
    omex
    cflim2
    mpbi
    @0
    limomss
    ax-mp
    eqssi
end
