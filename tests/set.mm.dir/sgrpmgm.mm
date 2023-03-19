include "csgrp.mm"
include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "issgrp.mm"
include "simplbi.mm"

theorem sgrpmgm
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( M e. SGrp -> M e. Mgm )

  proof
    cM
    csgrp
    wcel
    cM
    cmgm
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    vz
    cv
    #
    @2
    co
    @0
    @1
    @3
    @2
    co
    @2
    co
    wceq
    vz
    cM
    cbs
    cfv
    #
    wral
    vy
    @4
    wral
    vx
    @4
    wral
    vx
    vy
    vz
    @4
    cM
    @2
    @4
    eqid
    @2
    eqid
    issgrp
    simplbi
end
