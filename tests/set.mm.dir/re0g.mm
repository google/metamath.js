include "ccnfld.mm"
include "cmnd.mm"
include "wcel.mm"
include "cc0.mm"
include "cr.mm"
include "cc.mm"
include "wss.mm"
include "crefld.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "ccrg.mm"
include "crg.mm"
include "cncrng.mm"
include "crngring.mm"
include "ringmnd.mm"
include "mp2b.mm"
include "0re.mm"
include "ax-resscn.mm"
include "df-refld.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "ress0g.mm"
include "mp3an.mm"

theorem re0g



  assert |- 0 = ( 0g ` RRfld )

  proof
    ccnfld
    cmnd
    wcel
    #
    cc0
    cr
    wcel
    cr
    cc
    wss
    cc0
    crefld
    c0g
    cfv
    wceq
    ccnfld
    ccrg
    wcel
    ccnfld
    crg
    wcel
    @0
    cncrng
    ccnfld
    crngring
    ccnfld
    ringmnd
    mp2b
    0re
    ax-resscn
    cr
    cc
    ccnfld
    crefld
    cc0
    df-refld
    cnfldbas
    cnfld0
    ress0g
    mp3an
end
