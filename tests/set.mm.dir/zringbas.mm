include "cz.mm"
include "cc.mm"
include "wss.mm"
include "zring.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "zsscn.mm"
include "ccnfld.mm"
include "df-zring.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"

theorem zringbas



  assert |- ZZ = ( Base ` ZZring )

  proof
    cz
    cc
    wss
    cz
    zring
    cbs
    cfv
    wceq
    zsscn
    cz
    cc
    zring
    ccnfld
    df-zring
    cnfldbas
    ressbas2
    ax-mp
end
