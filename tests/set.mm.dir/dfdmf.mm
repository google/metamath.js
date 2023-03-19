include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "df-dm.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq2.mm"
include "cbvex.mm"
include "abbii.mm"
include "nfex.mm"
include "weq.mm"
include "breq1.mm"
include "exbidv.mm"
include "cbvab.mm"
include "3eqtri.mm"

theorem dfdmf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  assume dfdmf.1: |- F/_ x A
  assume dfdmf.2: |- F/_ y A

  disjoint x y
  disjoint w x
  disjoint v x
  disjoint w y
  disjoint v y
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- dom A = { x | E. y x A y }

  proof
    cA
    cdm
    vw
    cv
    #
    vv
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
    @0
    vy
    cv
    #
    cA
    wbr
    #
    vy
    wex
    #
    vw
    cab
    vx
    cv
    #
    @4
    cA
    wbr
    #
    vy
    wex
    #
    vx
    cab
    vw
    vv
    cA
    df-dm
    @3
    @6
    vw
    @2
    @5
    vv
    vy
    vy
    @0
    @1
    cA
    vy
    @0
    nfcv
    dfdmf.2
    vy
    @1
    nfcv
    nfbr
    @5
    vv
    nfv
    @1
    @4
    @0
    cA
    breq2
    cbvex
    abbii
    @6
    @9
    vw
    vx
    @5
    vx
    vy
    vx
    @0
    @4
    cA
    vx
    @0
    nfcv
    dfdmf.1
    vx
    @4
    nfcv
    nfbr
    nfex
    @9
    vw
    nfv
    vw
    vx
    weq
    @5
    @8
    vy
    @0
    @7
    @4
    cA
    breq1
    exbidv
    cbvab
    3eqtri
end
