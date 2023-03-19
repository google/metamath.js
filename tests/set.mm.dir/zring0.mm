include "ccnfld.mm"
include "cmnd.mm"
include "wcel.mm"
include "cc0.mm"
include "cz.mm"
include "cc.mm"
include "wss.mm"
include "zring.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "ccrg.mm"
include "crg.mm"
include "cncrng.mm"
include "crngring.mm"
include "ringmnd.mm"
include "mp2b.mm"
include "0z.mm"
include "zsscn.mm"
include "df-zring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "ress0g.mm"
include "mp3an.mm"

theorem zring0



  assert |- 0 = ( 0g ` ZZring )

  proof
    ccnfld
    cmnd
    wcel
    #
    cc0
    cz
    wcel
    cz
    cc
    wss
    cc0
    zring
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
    0z
    zsscn
    cz
    cc
    ccnfld
    zring
    cc0
    df-zring
    cnfldbas
    cnfld0
    ress0g
    mp3an
end
