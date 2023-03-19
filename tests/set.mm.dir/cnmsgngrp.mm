include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "csubg.mm"
include "wcel.mm"
include "cgrp.mm"
include "eqid.mm"
include "cnmsgnsubg.mm"
include "cvv.mm"
include "wss.mm"
include "wceq.mm"
include "cnex.mm"
include "difss.mm"
include "ssexi.mm"
include "wne.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "prssi.mm"
include "mp2an.mm"
include "ressabs.mm"
include "eqtr4i.mm"
include "subggrp.mm"
include "ax-mp.mm"

theorem cnmsgngrp
  let cU: class U
  assume cnmsgngrp.u: |- U = ( ( mulGrp ` CCfld ) |`s { 1 , -u 1 } )


  assert |- U e. Grp

  proof
    c1
    c1
    cneg
    #
    cpr
    #
    ccnfld
    cmgp
    cfv
    #
    cc
    cc0
    csn
    #
    cdif
    #
    cress
    co
    #
    csubg
    cfv
    wcel
    cU
    cgrp
    wcel
    @5
    @5
    eqid
    cnmsgnsubg
    @1
    @5
    cU
    cU
    @2
    @1
    cress
    co
    #
    @5
    @1
    cress
    co
    #
    cnmsgngrp.u
    @4
    cvv
    wcel
    @1
    @4
    wss
    #
    @7
    @6
    wceq
    @4
    cc
    cnex
    cc
    @3
    difss
    ssexi
    c1
    @4
    wcel
    #
    @0
    @4
    wcel
    #
    @8
    @9
    c1
    cc
    wcel
    c1
    cc0
    wne
    ax-1cn
    ax-1ne0
    c1
    cc
    cc0
    eldifsn
    mpbir2an
    @10
    @0
    cc
    wcel
    @0
    cc0
    wne
    neg1cn
    neg1ne0
    @0
    cc
    cc0
    eldifsn
    mpbir2an
    c1
    @0
    @4
    prssi
    mp2an
    @4
    @1
    @2
    cvv
    ressabs
    mp2an
    eqtr4i
    subggrp
    ax-mp
end
