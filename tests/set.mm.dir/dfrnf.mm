include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "dfrn2.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1.mm"
include "cbvex.mm"
include "abbii.mm"
include "nfex.mm"
include "weq.mm"
include "breq2.mm"
include "exbidv.mm"
include "cbvab.mm"
include "3eqtri.mm"

theorem dfrnf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  assume dfrnf.1: |- F/_ x A
  assume dfrnf.2: |- F/_ y A

  disjoint x y
  disjoint w x
  disjoint v x
  disjoint w y
  disjoint v y
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- ran A = { y | E. x x A y }

  proof
    cA
    crn
    vv
    cv
    #
    vw
    cv
    #
    cA
    wbr
    #
    vv
    wex
    #
    vw
    cab
    vx
    cv
    #
    @1
    cA
    wbr
    #
    vx
    wex
    #
    vw
    cab
    @4
    vy
    cv
    #
    cA
    wbr
    #
    vx
    wex
    #
    vy
    cab
    vv
    vw
    cA
    dfrn2
    @3
    @6
    vw
    @2
    @5
    vv
    vx
    vx
    @0
    @1
    cA
    vx
    @0
    nfcv
    dfrnf.1
    vx
    @1
    nfcv
    nfbr
    @5
    vv
    nfv
    @0
    @4
    @1
    cA
    breq1
    cbvex
    abbii
    @6
    @9
    vw
    vy
    @5
    vy
    vx
    vy
    @4
    @1
    cA
    vy
    @4
    nfcv
    dfrnf.2
    vy
    @1
    nfcv
    nfbr
    nfex
    @9
    vw
    nfv
    vw
    vy
    weq
    @5
    @8
    vx
    @1
    @7
    @4
    cA
    breq2
    exbidv
    cbvab
    3eqtri
end
