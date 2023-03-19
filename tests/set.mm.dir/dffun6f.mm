include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "wmo.mm"
include "dffun3.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq2.mm"
include "cbvmo.mm"
include "albii.mm"
include "mo2v.mm"
include "nfmo.mm"
include "breq1.mm"
include "mobidv.mm"
include "cbval.mm"
include "3bitr3ri.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem dffun6f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assume dffun6f.1: |- F/_ x A
  assume dffun6f.2: |- F/_ y A

  disjoint x y
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint A w
  disjoint A v
  disjoint A u
  assert |- ( Fun A <-> ( Rel A /\ A. x E* y x A y ) )

  proof
    cA
    wfun
    cA
    wrel
    #
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
    vu
    weq
    wi
    vv
    wal
    vu
    wex
    #
    vw
    wal
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    wa
    vw
    vv
    vu
    cA
    dffun3
    @10
    @5
    @0
    @3
    vv
    wmo
    #
    vw
    wal
    @1
    @7
    cA
    wbr
    #
    vy
    wmo
    #
    vw
    wal
    @5
    @10
    @11
    @13
    vw
    @3
    @12
    vv
    vy
    vy
    @1
    @2
    cA
    vy
    @1
    nfcv
    dffun6f.2
    vy
    @2
    nfcv
    nfbr
    @12
    vv
    nfv
    @2
    @7
    @1
    cA
    breq2
    cbvmo
    albii
    @11
    @4
    vw
    @3
    vv
    vu
    mo2v
    albii
    @13
    @9
    vw
    vx
    @12
    vx
    vy
    vx
    @1
    @7
    cA
    vx
    @1
    nfcv
    dffun6f.1
    vx
    @7
    nfcv
    nfbr
    nfmo
    @9
    vw
    nfv
    vw
    vx
    weq
    @12
    @8
    vy
    @1
    @6
    @7
    cA
    breq1
    mobidv
    cbval
    3bitr3ri
    anbi2i
    bitr4i
end
