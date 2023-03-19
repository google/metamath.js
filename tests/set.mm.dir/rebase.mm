include "cr.mm"
include "cc.mm"
include "wss.mm"
include "crefld.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "ccnfld.mm"
include "df-refld.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"

theorem rebase



  assert |- RR = ( Base ` RRfld )

  proof
    cr
    cc
    wss
    cr
    crefld
    cbs
    cfv
    wceq
    ax-resscn
    cr
    cc
    crefld
    ccnfld
    df-refld
    cnfldbas
    ressbas2
    ax-mp
end
