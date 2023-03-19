include "cmgm2.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "casslaw.mm"
include "wbr.mm"
include "wa.mm"
include "cmgm.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "csgrp2.mm"
include "csgrp.mm"
include "mgm2mgm.mm"
include "anbi1i.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "isasslaw.mm"
include "mp1i.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "eqid.mm"
include "issgrpALT.mm"
include "issgrp.mm"
include "3bitr4i.mm"

theorem sgrp2sgrp
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( M e. SGrpALT <-> M e. SGrp )

  proof
    cM
    cmgm2
    wcel
    #
    cM
    cplusg
    cfv
    #
    cM
    cbs
    cfv
    #
    casslaw
    wbr
    #
    wa
    #
    cM
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    vz
    cv
    #
    @1
    co
    @6
    @7
    @8
    @1
    co
    @1
    co
    wceq
    vz
    @2
    wral
    vy
    @2
    wral
    vx
    @2
    wral
    #
    wa
    #
    cM
    csgrp2
    wcel
    cM
    csgrp
    wcel
    @4
    @5
    @3
    wa
    @10
    @0
    @5
    @3
    cM
    mgm2mgm
    anbi1i
    @5
    @3
    @9
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    @3
    @9
    wb
    @5
    @11
    @12
    cM
    cplusg
    fvex
    cM
    cbs
    fvex
    pm3.2i
    vx
    vy
    vz
    @2
    cvv
    cvv
    @1
    isasslaw
    mp1i
    pm5.32i
    bitri
    @2
    cM
    @1
    @2
    eqid
    #
    @1
    eqid
    #
    issgrpALT
    vx
    vy
    vz
    @2
    cM
    @1
    @13
    @14
    issgrp
    3bitr4i
end
