include "wrel.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ssel.mm"
include "alrimivv.mm"
include "wceq.mm"
include "wex.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "biimprcd.mm"
include "2alimi.mm"
include "19.23vv.mm"
include "sylib.mm"
include "com23.mm"
include "a2d.mm"
include "alimdv.mm"
include "cvv.mm"
include "cxp.mm"
include "df-rel.mm"
include "dfss2.mm"
include "elvv.mm"
include "imbi2i.mm"
include "albii.mm"
include "3bitri.mm"
include "3imtr4g.mm"
include "com12.mm"
include "impbid2.mm"

theorem ssrelOLD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( Rel A -> ( A C_ B <-> A. x A. y ( <. x , y >. e. A -> <. x , y >. e. B ) ) )

  proof
    cA
    wrel
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
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @1
    @5
    vx
    vy
    cA
    cB
    @2
    ssel
    alrimivv
    @6
    @0
    @1
    @6
    vz
    cv
    #
    cA
    wcel
    #
    @7
    @2
    wceq
    #
    vy
    wex
    vx
    wex
    #
    wi
    #
    vz
    wal
    #
    @8
    @7
    cB
    wcel
    #
    wi
    #
    vz
    wal
    @0
    @1
    @6
    @11
    @14
    vz
    @6
    @8
    @10
    @13
    @6
    @10
    @8
    @13
    @6
    @9
    @14
    wi
    #
    vy
    wal
    vx
    wal
    @10
    @14
    wi
    @5
    @15
    vx
    vy
    @9
    @14
    @5
    @9
    @8
    @3
    @13
    @4
    @7
    @2
    cA
    eleq1
    @7
    @2
    cB
    eleq1
    imbi12d
    biimprcd
    2alimi
    @9
    @14
    vx
    vy
    19.23vv
    sylib
    com23
    a2d
    alimdv
    @0
    cA
    cvv
    cvv
    cxp
    #
    wss
    @8
    @7
    @16
    wcel
    #
    wi
    #
    vz
    wal
    @12
    cA
    df-rel
    vz
    cA
    @16
    dfss2
    @18
    @11
    vz
    @17
    @10
    @8
    vx
    vy
    @7
    elvv
    imbi2i
    albii
    3bitri
    vz
    cA
    cB
    dfss2
    3imtr4g
    com12
    impbid2
end
