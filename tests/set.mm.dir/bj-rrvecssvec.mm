include "crrvec.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "crefld.mm"
include "wceq.mm"
include "clvec.mm"
include "crab.mm"
include "df-bj-rrvec.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem bj-rrvecssvec
  let vx: setvar x


  assert |- RRVec C_ LVec

  proof
    crrvec
    vx
    cv
    csca
    cfv
    crefld
    wceq
    #
    vx
    clvec
    crab
    clvec
    vx
    df-bj-rrvec
    @0
    vx
    clvec
    ssrab2
    eqsstri
end
