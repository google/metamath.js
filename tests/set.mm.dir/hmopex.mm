include "cho.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "ovex.mm"
include "cv.mm"
include "wcel.mm"
include "wf.mm"
include "hmopf.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "sylibr.mm"
include "ssriv.mm"
include "ssexi.mm"

theorem hmopex
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- HrmOp e. _V

  proof
    cho
    chil
    chil
    cmap
    co
    #
    chil
    chil
    cmap
    ovex
    vt
    cho
    @0
    vt
    cv
    #
    cho
    wcel
    chil
    chil
    @1
    wf
    @1
    @0
    wcel
    @1
    hmopf
    chil
    chil
    @1
    ax-hilex
    ax-hilex
    elmap
    sylibr
    ssriv
    ssexi
end
