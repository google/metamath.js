include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "fvclss.mm"
include "ssexi.mm"

theorem fvclex
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume fvclex.1: |- F e. _V

  disjoint x y
  disjoint F x
  disjoint F y
  assert |- { y | E. x y = ( F ` x ) } e. _V

  proof
    vy
    cv
    vx
    cv
    cF
    cfv
    wceq
    vx
    wex
    vy
    cab
    cF
    crn
    #
    c0
    csn
    #
    cun
    @0
    @1
    cF
    fvclex.1
    rnex
    p0ex
    unex
    vx
    vy
    cF
    fvclss
    ssexi
end
