include "ccmn.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cmnd.mm"
include "crab.mm"
include "df-cmn.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem bj-cmnssmnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- CMnd C_ Mnd

  proof
    ccmn
    vy
    cv
    #
    vz
    cv
    #
    vx
    cv
    #
    cplusg
    cfv
    #
    co
    @1
    @0
    @3
    co
    wceq
    vz
    @2
    cbs
    cfv
    #
    wral
    vy
    @4
    wral
    #
    vx
    cmnd
    crab
    cmnd
    vx
    vy
    vz
    df-cmn
    @5
    vx
    cmnd
    ssrab2
    eqsstri
end
