include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ssel.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "wceq.mm"
include "wex.mm"
include "elvvv.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "biimprcd.mm"
include "alimi.mm"
include "19.23v.mm"
include "sylib.mm"
include "2alimi.mm"
include "19.23vv.mm"
include "syl5bi.mm"
include "com23.mm"
include "a2d.mm"
include "alimdv.mm"
include "dfss2.mm"
include "3imtr4g.mm"
include "com12.mm"
include "impbid2.mm"

theorem ssrelrel
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  assert |- ( A C_ ( ( _V X. _V ) X. _V ) -> ( A C_ B <-> A. x A. y A. z ( <. <. x , y >. , z >. e. A -> <. <. x , y >. , z >. e. B ) ) )

  proof
    cA
    cvv
    cvv
    cxp
    cvv
    cxp
    #
    wss
    #
    cA
    cB
    wss
    #
    vx
    cv
    vy
    cv
    cop
    vz
    cv
    cop
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    @2
    @7
    vx
    vy
    @2
    @6
    vz
    cA
    cB
    @3
    ssel
    alrimiv
    alrimivv
    @8
    @1
    @2
    @8
    vw
    cv
    #
    cA
    wcel
    #
    @9
    @0
    wcel
    #
    wi
    #
    vw
    wal
    @10
    @9
    cB
    wcel
    #
    wi
    #
    vw
    wal
    @1
    @2
    @8
    @12
    @14
    vw
    @8
    @10
    @11
    @13
    @8
    @11
    @10
    @13
    @11
    @9
    @3
    wceq
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @8
    @14
    vx
    vy
    vz
    @9
    elvvv
    @8
    @16
    @14
    wi
    #
    vy
    wal
    vx
    wal
    @17
    @14
    wi
    @7
    @18
    vx
    vy
    @7
    @15
    @14
    wi
    #
    vz
    wal
    @18
    @6
    @19
    vz
    @15
    @14
    @6
    @15
    @10
    @4
    @13
    @5
    @9
    @3
    cA
    eleq1
    @9
    @3
    cB
    eleq1
    imbi12d
    biimprcd
    alimi
    @15
    @14
    vz
    19.23v
    sylib
    2alimi
    @16
    @14
    vx
    vy
    19.23vv
    sylib
    syl5bi
    com23
    a2d
    alimdv
    vw
    cA
    @0
    dfss2
    vw
    cA
    cB
    dfss2
    3imtr4g
    com12
    impbid2
end
