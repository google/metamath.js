include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "csingles.mm"
include "elsingles.mm"
include "abbi2i.mm"

theorem dfsingles2
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- Singletons = { x | E. y x = { y } }

  proof
    vx
    cv
    #
    vy
    cv
    csn
    wceq
    vy
    wex
    vx
    csingles
    vy
    @0
    elsingles
    abbi2i
end
