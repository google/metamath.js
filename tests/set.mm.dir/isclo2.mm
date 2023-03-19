include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "isclo.mm"
include "weq.mm"
include "eleq1.mm"
include "bibi2d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "pm4.24.mm"
include "raaanv.mm"
include "3bitr4i.mm"
include "bibi1.mm"
include "biimpa.mm"
include "biimpcd.mm"
include "ralimdv.mm"
include "com12.mm"
include "dfss3.mm"
include "syl6ibr.mm"
include "ralimi.mm"
include "sylbi.mm"
include "imbi1d.mm"
include "rspcv.mm"
include "imbi2i.mm"
include "r19.21v.mm"
include "bitr4i.mm"
include "syl6ib.mm"
include "ssel.mm"
include "imim2d.mm"
include "jcad.mm"
include "ralbiim.mm"
include "impbid2.mm"
include "pm5.32i.mm"
include "rexbii.mm"
include "ralbii.mm"
include "syl6bb.mm"

theorem isclo2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cJ: class J
  let cX: class X
  let vw: setvar w
  assume isclo.1: |- X = U. J

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  assert |- ( ( J e. Top /\ A C_ X ) -> ( A e. ( J i^i ( Clsd ` J ) ) <-> A. x e. X E. y e. J ( x e. y /\ A. z e. y ( z e. A -> y C_ A ) ) ) )

  proof
    cJ
    ctop
    wcel
    cA
    cX
    wss
    wa
    cA
    cJ
    cJ
    ccld
    cfv
    cin
    wcel
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @0
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    wb
    #
    vz
    @1
    wral
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    cX
    wral
    @2
    @5
    @1
    cA
    wss
    #
    wi
    #
    vz
    @1
    wral
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    cX
    wral
    vx
    vy
    vz
    cA
    cJ
    cX
    isclo.1
    isclo
    @9
    @14
    vx
    cX
    @8
    @13
    vy
    cJ
    @2
    @7
    @12
    @2
    @7
    @12
    @7
    @6
    @3
    vw
    cv
    #
    cA
    wcel
    #
    wb
    #
    wa
    #
    vw
    @1
    wral
    #
    vz
    @1
    wral
    #
    @12
    @7
    @7
    wa
    @7
    @17
    vw
    @1
    wral
    #
    wa
    @7
    @20
    @7
    @21
    @7
    @6
    @17
    vz
    vw
    @1
    vz
    vw
    weq
    @5
    @16
    @3
    @4
    @15
    cA
    eleq1
    bibi2d
    cbvralv
    anbi2i
    @7
    pm4.24
    @6
    @17
    vz
    vw
    @1
    raaanv
    3bitr4i
    @19
    @11
    vz
    @1
    @19
    @5
    @16
    vw
    @1
    wral
    #
    @10
    @5
    @19
    @22
    @5
    @18
    @16
    vw
    @1
    @18
    @5
    @16
    @6
    @17
    @5
    @16
    wb
    @3
    @5
    @16
    bibi1
    biimpa
    biimpcd
    ralimdv
    com12
    vw
    @1
    cA
    dfss3
    syl6ibr
    ralimi
    sylbi
    @2
    @12
    @3
    @5
    wi
    vz
    @1
    wral
    #
    @5
    @3
    wi
    #
    vz
    @1
    wral
    #
    wa
    @7
    @2
    @12
    @23
    @25
    @2
    @12
    @3
    @10
    wi
    #
    @23
    @11
    @26
    vz
    @0
    @1
    vz
    vx
    weq
    @5
    @3
    @10
    @4
    @0
    cA
    eleq1
    imbi1d
    rspcv
    @26
    @3
    @5
    vz
    @1
    wral
    #
    wi
    @23
    @10
    @27
    @3
    vz
    @1
    cA
    dfss3
    imbi2i
    @3
    @5
    vz
    @1
    r19.21v
    bitr4i
    syl6ib
    @2
    @11
    @24
    vz
    @1
    @2
    @10
    @3
    @5
    @10
    @2
    @3
    @1
    cA
    @0
    ssel
    com12
    imim2d
    ralimdv
    jcad
    @3
    @5
    vz
    @1
    ralbiim
    syl6ibr
    impbid2
    pm5.32i
    rexbii
    ralbii
    syl6bb
end
