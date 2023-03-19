include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "prssi.mm"
include "mp2an.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "eqid.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"

theorem cnmsgnbas
  let cU: class U
  assume cnmsgngrp.u: |- U = ( ( mulGrp ` CCfld ) |`s { 1 , -u 1 } )


  assert |- { 1 , -u 1 } = ( Base ` U )

  proof
    c1
    c1
    cneg
    #
    cpr
    #
    cc
    wss
    #
    @1
    cU
    cbs
    cfv
    wceq
    c1
    cc
    wcel
    @0
    cc
    wcel
    @2
    ax-1cn
    neg1cn
    c1
    @0
    cc
    prssi
    mp2an
    @1
    cc
    cU
    ccnfld
    cmgp
    cfv
    #
    cnmsgngrp.u
    cc
    ccnfld
    @3
    @3
    eqid
    cnfldbas
    mgpbas
    ressbas2
    ax-mp
end
