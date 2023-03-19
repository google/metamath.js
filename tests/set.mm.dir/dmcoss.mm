include "ccom.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "wbr.mm"
include "nfe1.mm"
include "wa.mm"
include "exsimpl.mm"
include "vex.mm"
include "opelco.mm"
include "breq2.mm"
include "cbvexv.mm"
include "3imtr4i.mm"
include "exlimi.mm"
include "eldm2.mm"
include "eldm.mm"
include "ssriv.mm"

theorem dmcoss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- dom ( A o. B ) C_ dom B

  proof
    vx
    cA
    cB
    ccom
    #
    cdm
    #
    cB
    cdm
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    @0
    wcel
    #
    vy
    wex
    @3
    @4
    cB
    wbr
    #
    vy
    wex
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    @5
    @7
    vy
    @6
    vy
    nfe1
    @3
    vz
    cv
    #
    cB
    wbr
    #
    @8
    @4
    cA
    wbr
    #
    wa
    vz
    wex
    @9
    vz
    wex
    @5
    @7
    @9
    @10
    vz
    exsimpl
    vz
    @3
    @4
    cA
    cB
    vx
    vex
    #
    vy
    vex
    opelco
    @6
    @9
    vy
    vz
    @4
    @8
    @3
    cB
    breq2
    cbvexv
    3imtr4i
    exlimi
    vy
    @3
    @0
    @11
    eldm2
    vy
    @3
    cB
    @11
    eldm
    3imtr4i
    ssriv
end
