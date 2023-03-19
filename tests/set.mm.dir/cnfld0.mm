include "ccnfld.mm"
include "c0g.mm"
include "cfv.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "00id.mm"
include "cgrp.mm"
include "wcel.mm"
include "cc.mm"
include "wb.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "0cn.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "eqid.mm"
include "grpid.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqcomi.mm"

theorem cnfld0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- 0 = ( 0g ` CCfld )

  proof
    ccnfld
    c0g
    cfv
    #
    cc0
    cc0
    cc0
    caddc
    co
    cc0
    wceq
    #
    @0
    cc0
    wceq
    #
    00id
    ccnfld
    cgrp
    wcel
    #
    cc0
    cc
    wcel
    @1
    @2
    wb
    ccnfld
    crg
    wcel
    @3
    cnring
    ccnfld
    ringgrp
    ax-mp
    0cn
    cc
    caddc
    ccnfld
    cc0
    @0
    cnfldbas
    cnfldadd
    @0
    eqid
    grpid
    mp2an
    mpbi
    eqcomi
end
