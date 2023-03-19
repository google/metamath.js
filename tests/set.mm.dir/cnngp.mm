include "ccnfld.mm"
include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmt.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "wss.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "cnfldms.mm"
include "ssid.mm"
include "cnfldnm.mm"
include "cnfldsub.mm"
include "cnfldds.mm"
include "isngp.mm"
include "mpbir3an.mm"

theorem cnngp



  assert |- CCfld e. NrmGrp

  proof
    ccnfld
    cngp
    wcel
    ccnfld
    cgrp
    wcel
    #
    ccnfld
    cmt
    wcel
    cabs
    cmin
    ccom
    #
    @1
    wss
    ccnfld
    crg
    wcel
    @0
    cnring
    ccnfld
    ringgrp
    ax-mp
    cnfldms
    @1
    ssid
    @1
    ccnfld
    cmin
    cabs
    cnfldnm
    cnfldsub
    cnfldds
    isngp
    mpbir3an
end
