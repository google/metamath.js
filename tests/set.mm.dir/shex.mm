include "csh.mm"
include "chil.mm"
include "cpw.mm"
include "ax-hilex.mm"
include "pwex.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "shss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "ssexi.mm"

theorem shex
  let vx: setvar x


  assert |- SH e. _V

  proof
    csh
    chil
    cpw
    #
    chil
    ax-hilex
    pwex
    vx
    csh
    @0
    vx
    cv
    #
    csh
    wcel
    @1
    chil
    wss
    @1
    @0
    wcel
    @1
    shss
    vx
    chil
    selpw
    sylibr
    ssriv
    ssexi
end
