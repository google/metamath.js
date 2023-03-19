include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "csgrp.mm"
include "casslaw.mm"
include "wbr.mm"
include "simpr.mm"
include "eqid.mm"
include "issgrp.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "isasslaw.mm"
include "mp2an.mm"
include "3imtr4i.mm"

theorem sgrpplusgaopALT
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( G e. SGrp -> ( +g ` G ) assLaw ( Base ` G ) )

  proof
    cG
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    vz
    cv
    #
    @3
    co
    @1
    @2
    @4
    @3
    co
    @3
    co
    wceq
    vz
    cG
    cbs
    cfv
    #
    wral
    vy
    @5
    wral
    vx
    @5
    wral
    #
    wa
    @6
    cG
    csgrp
    wcel
    @3
    @5
    casslaw
    wbr
    #
    @0
    @6
    simpr
    vx
    vy
    vz
    @5
    cG
    @3
    @5
    eqid
    @3
    eqid
    issgrp
    @3
    cvv
    wcel
    @5
    cvv
    wcel
    @7
    @6
    wb
    cG
    cplusg
    fvex
    cG
    cbs
    fvex
    vx
    vy
    vz
    @5
    cvv
    cvv
    @3
    isasslaw
    mp2an
    3imtr4i
end
