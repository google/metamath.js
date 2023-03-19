include "wel.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cdif.mm"
include "cdom.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "wex.mm"
include "cin.mm"
include "wcel.mm"
include "axgroth3.mm"
include "weq.mm"
include "elequ2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "cbvrexv.mm"
include "anbi2i.mm"
include "r19.42v.mm"
include "sseq1.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "19.26.mm"
include "pm4.76.mm"
include "elin.mm"
include "imbi2i.mm"
include "bitr4i.mm"
include "albii.mm"
include "3bitr2i.mm"
include "rexbii.mm"
include "ralbii.mm"
include "3anbi2i.mm"
include "exbii.mm"
include "mpbi.mm"

theorem axgroth4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  assert |- E. y ( x e. y /\ A. z e. y E. v e. y A. w ( w C_ z -> w e. ( y i^i v ) ) /\ A. z ( z C_ y -> ( ( y \ z ) ~<_ z \/ z e. y ) ) )

  proof
    vx
    vy
    wel
    #
    vw
    cv
    #
    vz
    cv
    #
    wss
    #
    vw
    vy
    wel
    #
    wi
    #
    vw
    wal
    #
    vu
    cv
    #
    @2
    wss
    #
    vu
    vw
    wel
    #
    wi
    #
    vu
    wal
    #
    vw
    vy
    cv
    #
    wrex
    #
    wa
    #
    vz
    @12
    wral
    #
    @2
    @12
    wss
    @12
    @2
    cdif
    @2
    cdom
    wbr
    vz
    vy
    wel
    wo
    wi
    vz
    wal
    #
    w3a
    #
    vy
    wex
    @0
    @3
    @1
    @12
    vv
    cv
    #
    cin
    wcel
    #
    wi
    #
    vw
    wal
    #
    vv
    @12
    wrex
    #
    vz
    @12
    wral
    #
    @16
    w3a
    #
    vy
    wex
    vx
    vy
    vz
    vw
    vu
    axgroth3
    @17
    @24
    vy
    @15
    @23
    @0
    @16
    @14
    @22
    vz
    @12
    @14
    @6
    @8
    vu
    vv
    wel
    #
    wi
    #
    vu
    wal
    #
    vv
    @12
    wrex
    #
    wa
    @6
    @27
    wa
    #
    vv
    @12
    wrex
    @22
    @13
    @28
    @6
    @11
    @27
    vw
    vv
    @12
    vw
    vv
    weq
    #
    @10
    @26
    vu
    @30
    @9
    @25
    @8
    vw
    vv
    vu
    elequ2
    imbi2d
    albidv
    cbvrexv
    anbi2i
    @6
    @27
    vv
    @12
    r19.42v
    @29
    @21
    vv
    @12
    @29
    @6
    @3
    vw
    vv
    wel
    #
    wi
    #
    vw
    wal
    #
    wa
    @5
    @32
    wa
    #
    vw
    wal
    @21
    @27
    @33
    @6
    @26
    @32
    vu
    vw
    vu
    vw
    weq
    @8
    @3
    @25
    @31
    @7
    @1
    @2
    sseq1
    vu
    vw
    vv
    elequ1
    imbi12d
    cbvalv
    anbi2i
    @5
    @32
    vw
    19.26
    @34
    @20
    vw
    @34
    @3
    @4
    @31
    wa
    #
    wi
    @20
    @3
    @4
    @31
    pm4.76
    @19
    @35
    @3
    @1
    @12
    @18
    elin
    imbi2i
    bitr4i
    albii
    3bitr2i
    rexbii
    3bitr2i
    ralbii
    3anbi2i
    exbii
    mpbi
end
