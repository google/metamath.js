include "wel.mm"
include "wn.mm"
include "cab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-ru1.mm"
include "bj-elissetv.mm"
include "mto.mm"

theorem bj-ru
  let vx: setvar x
  let cV: class V
  let vy: setvar y


  assert |- -. { x | -. x e. x } e. V

  proof
    vx
    vx
    wel
    wn
    vx
    cab
    #
    cV
    wcel
    vy
    cv
    @0
    wceq
    vy
    wex
    vx
    vy
    bj-ru1
    vy
    @0
    cV
    bj-elissetv
    mto
end
