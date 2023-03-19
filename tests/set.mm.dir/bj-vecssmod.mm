include "clvec.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "wcel.mm"
include "clmod.mm"
include "crab.mm"
include "df-lvec.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem bj-vecssmod
  let vx: setvar x


  assert |- LVec C_ LMod

  proof
    clvec
    vx
    cv
    csca
    cfv
    cdr
    wcel
    #
    vx
    clmod
    crab
    clmod
    vx
    df-lvec
    @0
    vx
    clmod
    ssrab2
    eqsstri
end
