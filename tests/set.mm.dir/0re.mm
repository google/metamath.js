include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wrex.mm"
include "1re.mm"
include "ax-rnegex.mm"
include "readdcl.mm"
include "mpan.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "mp2b.mm"

theorem 0re
  let vx: setvar x


  assert |- 0 e. RR

  proof
    c1
    cr
    wcel
    #
    c1
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
    cr
    wrex
    cc0
    cr
    wcel
    #
    1re
    vx
    c1
    ax-rnegex
    @3
    @4
    vx
    cr
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @3
    @4
    @0
    @5
    @6
    1re
    c1
    @1
    readdcl
    mpan
    @2
    cc0
    cr
    eleq1
    syl5ibcom
    rexlimiv
    mp2b
end
