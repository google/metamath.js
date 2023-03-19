include "cc.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cminusg.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "negid.mm"
include "wb.mm"
include "negcl.mm"
include "cgrp.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "cnfld0.mm"
include "eqid.mm"
include "grpinvid1.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem cnfldneg
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( X e. CC -> ( ( invg ` CCfld ) ` X ) = -u X )

  proof
    cX
    cc
    wcel
    #
    cX
    ccnfld
    cminusg
    cfv
    #
    cfv
    cX
    cneg
    #
    wceq
    #
    cX
    @2
    caddc
    co
    cc0
    wceq
    #
    cX
    negid
    @0
    @2
    cc
    wcel
    #
    @3
    @4
    wb
    #
    cX
    negcl
    ccnfld
    cgrp
    wcel
    #
    @0
    @5
    @6
    ccnfld
    crg
    wcel
    @7
    cnring
    ccnfld
    ringgrp
    ax-mp
    cc
    caddc
    ccnfld
    @1
    cX
    @2
    cc0
    cnfldbas
    cnfldadd
    cnfld0
    @1
    eqid
    grpinvid1
    mp3an1
    mpdan
    mpbird
end
