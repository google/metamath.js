include "ccnfld.mm"
include "ctgp.mm"
include "wcel.mm"
include "cgrp.mm"
include "ctps.mm"
include "cmin.mm"
include "ctopn.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "cnfldtps.mm"
include "eqid.mm"
include "subcn.mm"
include "cnfldsub.mm"
include "istgp2.mm"
include "mpbir3an.mm"

theorem cnfldtgp



  assert |- CCfld e. TopGrp

  proof
    ccnfld
    ctgp
    wcel
    ccnfld
    cgrp
    wcel
    #
    ccnfld
    ctps
    wcel
    cmin
    ccnfld
    ctopn
    cfv
    #
    @1
    ctx
    co
    @1
    ccn
    co
    wcel
    ccnfld
    crg
    wcel
    @0
    cnring
    ccnfld
    ringgrp
    ax-mp
    cnfldtps
    @1
    @1
    eqid
    #
    subcn
    ccnfld
    @1
    cmin
    @2
    cnfldsub
    istgp2
    mpbir3an
end
