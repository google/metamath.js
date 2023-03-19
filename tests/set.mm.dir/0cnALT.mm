include "ci.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "wcel.mm"
include "ax-icn.mm"
include "cnegex.mm"
include "ax-mp.mm"
include "addcl.mm"
include "mpan.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"

theorem 0cnALT
  let vx: setvar x


  assert |- 0 e. CC

  proof
    ci
    vx
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vx
    cc
    wrex
    #
    cc0
    cc
    wcel
    #
    ci
    cc
    wcel
    #
    @3
    ax-icn
    vx
    ci
    cnegex
    ax-mp
    @2
    @4
    vx
    cc
    @0
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @2
    @4
    @5
    @6
    @7
    ax-icn
    ci
    @0
    addcl
    mpan
    @1
    cc0
    cc
    eleq1
    syl5ibcom
    rexlimiv
    ax-mp
end
