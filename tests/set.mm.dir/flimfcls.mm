include "cflim.mm"
include "co.mm"
include "cfcls.mm"
include "cv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "cfil.mm"
include "cfv.mm"
include "ccl.mm"
include "wral.mm"
include "flimtop.mm"
include "eqid.mm"
include "flimfil.mm"
include "flimclsi.mm"
include "sseld.mm"
include "com12.mm"
include "ralrimiv.mm"
include "isfcls.mm"
include "syl3anbrc.mm"
include "ssriv.mm"

theorem flimfcls
  let cF: class F
  let cJ: class J
  let va: setvar a
  let vx: setvar x


  assert |- ( J fLim F ) C_ ( J fClus F )

  proof
    va
    cJ
    cF
    cflim
    co
    #
    cJ
    cF
    cfcls
    co
    #
    va
    cv
    #
    @0
    wcel
    #
    cJ
    ctop
    wcel
    cF
    cJ
    cuni
    #
    cfil
    cfv
    wcel
    @2
    vx
    cv
    #
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    vx
    cF
    wral
    @2
    @1
    wcel
    @2
    cF
    cJ
    flimtop
    @2
    cF
    cJ
    @4
    @4
    eqid
    #
    flimfil
    @3
    @7
    vx
    cF
    @5
    cF
    wcel
    #
    @3
    @7
    @9
    @0
    @6
    @2
    @5
    cF
    cJ
    flimclsi
    sseld
    com12
    ralrimiv
    @2
    cF
    cJ
    @4
    vx
    @8
    isfcls
    syl3anbrc
    ssriv
end
