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
include "cvv.mm"
include "cxp.mm"
include "df-rel.mm"
include "dfss2.mm"
include "sylbb.mm"
include "wa.mm"
include "copab.mm"
include "cab.mm"
include "df-xp.mm"
include "df-opab.mm"
include "eqtri.mm"
include "abeq2i.mm"
include "simpl.mm"
include "2eximi.mm"
include "sylbi.mm"
include "imim2i.mm"
include "sylg.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "biimprcd.mm"
include "2alimi.mm"
include "19.23vv.mm"
include "sylib.mm"
include "com23.mm"
include "a2d.mm"
include "alimdv.mm"
include "syl5.mm"
include "syl6ibr.mm"
include "com12.mm"
include "impbid2.mm"

theorem ssrel
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
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @4
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
    @7
    vx
    vy
    cA
    cB
    @4
    ssel
    alrimivv
    @8
    @0
    @1
    @8
    @0
    vz
    cv
    #
    cA
    wcel
    #
    @9
    cB
    wcel
    #
    wi
    #
    vz
    wal
    #
    @1
    @0
    @10
    @9
    @4
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
    @8
    @13
    @0
    @10
    @9
    cvv
    cvv
    cxp
    #
    wcel
    #
    wi
    #
    @16
    vz
    @0
    cA
    @17
    wss
    @19
    vz
    wal
    cA
    df-rel
    vz
    cA
    @17
    dfss2
    sylbb
    @18
    @15
    @10
    @18
    @14
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @15
    @22
    vz
    @17
    @17
    @20
    vx
    vy
    copab
    @22
    vz
    cab
    vx
    vy
    cvv
    cvv
    df-xp
    @20
    vx
    vy
    vz
    df-opab
    eqtri
    abeq2i
    @21
    @14
    vx
    vy
    @14
    @20
    simpl
    2eximi
    sylbi
    imim2i
    sylg
    @8
    @16
    @12
    vz
    @8
    @10
    @15
    @11
    @8
    @15
    @10
    @11
    @8
    @14
    @12
    wi
    #
    vy
    wal
    vx
    wal
    @15
    @12
    wi
    @7
    @23
    vx
    vy
    @14
    @12
    @7
    @14
    @10
    @5
    @11
    @6
    @9
    @4
    cA
    eleq1
    @9
    @4
    cB
    eleq1
    imbi12d
    biimprcd
    2alimi
    @14
    @12
    vx
    vy
    19.23vv
    sylib
    com23
    a2d
    alimdv
    syl5
    vz
    cA
    cB
    dfss2
    syl6ibr
    com12
    impbid2
end
