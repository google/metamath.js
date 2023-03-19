include "wrel.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "nfss.mm"
include "ssel.mm"
include "alrimi.mm"
include "wceq.mm"
include "wex.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "biimprcd.mm"
include "2alimi.mm"
include "nfcri.mm"
include "nfim.mm"
include "19.23.mm"
include "albii.mm"
include "bitri.mm"
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
include "3bitri.mm"
include "3imtr4g.mm"
include "com12.mm"
include "impbid2.mm"

theorem ssrelf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume eqrelrd2.1: |- F/ x ph
  assume eqrelrd2.2: |- F/ y ph
  assume eqrelrd2.3: |- F/_ x A
  assume eqrelrd2.4: |- F/_ y A
  assume eqrelrd2.5: |- F/_ x B
  assume eqrelrd2.6: |- F/_ y B

  disjoint x y
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
    #
    vx
    wal
    #
    @1
    @6
    vx
    vx
    cA
    cB
    eqrelrd2.3
    eqrelrd2.5
    nfss
    @1
    @5
    vy
    vy
    cA
    cB
    eqrelrd2.4
    eqrelrd2.6
    nfss
    cA
    cB
    @2
    ssel
    alrimi
    alrimi
    @7
    @0
    @1
    @7
    vz
    cv
    #
    cA
    wcel
    #
    @8
    @2
    wceq
    #
    vy
    wex
    #
    vx
    wex
    #
    wi
    #
    vz
    wal
    #
    @9
    @8
    cB
    wcel
    #
    wi
    #
    vz
    wal
    @0
    @1
    @7
    @13
    @16
    vz
    @7
    @9
    @12
    @15
    @7
    @12
    @9
    @15
    @7
    @10
    @16
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @12
    @16
    wi
    #
    @5
    @17
    vx
    vy
    @10
    @16
    @5
    @10
    @9
    @3
    @15
    @4
    @8
    @2
    cA
    eleq1
    @8
    @2
    cB
    eleq1
    imbi12d
    biimprcd
    2alimi
    @19
    @11
    @16
    wi
    #
    vx
    wal
    @20
    @18
    @21
    vx
    @10
    @16
    vy
    @9
    @15
    vy
    vy
    vz
    cA
    eqrelrd2.4
    nfcri
    vy
    vz
    cB
    eqrelrd2.6
    nfcri
    nfim
    19.23
    albii
    @11
    @16
    vx
    @9
    @15
    vx
    vx
    vz
    cA
    eqrelrd2.3
    nfcri
    vx
    vz
    cB
    eqrelrd2.5
    nfcri
    nfim
    19.23
    bitri
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
    @9
    @8
    @22
    wcel
    #
    wi
    #
    vz
    wal
    @14
    cA
    df-rel
    vz
    cA
    @22
    dfss2
    @24
    @13
    vz
    @23
    @12
    @9
    vx
    vy
    @8
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
