include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "trcleq2lem.mm"
include "cbvabv.mm"

theorem cvbtrcl
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint x y
  disjoint R x
  disjoint R y
  assert |- { x | ( R C_ x /\ ( x o. x ) C_ x ) } = { y | ( R C_ y /\ ( y o. y ) C_ y ) }

  proof
    cR
    vx
    cv
    #
    wss
    @0
    @0
    ccom
    @0
    wss
    wa
    cR
    vy
    cv
    #
    wss
    @1
    @1
    ccom
    @1
    wss
    wa
    vx
    vy
    @0
    @1
    cR
    trcleq2lem
    cbvabv
end
