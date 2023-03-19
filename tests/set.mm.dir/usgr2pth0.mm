include "cusgr.mm"
include "wcel.mm"
include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1.mm"
include "cfz.mm"
include "cv.mm"
include "c1.mm"
include "w3a.mm"
include "cpr.mm"
include "cdif.mm"
include "wrex.mm"
include "csn.mm"
include "usgr2pth.mm"
include "wb.mm"
include "wne.mm"
include "r19.42v.mm"
include "rexdifpr.mm"
include "bitr3i.mm"
include "rexbii.mm"
include "rexcom.mm"
include "df-3an.mm"
include "anass.mm"
include "ancom.mm"
include "necom.mm"
include "anbi2ci.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "3bitr2i.mm"
include "rexdifsn.mm"
include "a1i.mm"
include "rexbidva.mm"
include "3anbi3d.mm"
include "bitrd.mm"

theorem usgr2pth0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vi: setvar i
  assume usgr2pthlem.v: |- V = ( Vtx ` G )
  assume usgr2pthlem.i: |- I = ( iEdg ` G )

  disjoint F x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint F i
  disjoint I i
  disjoint P i
  disjoint G i
  disjoint V i
  assert |- ( G e. USGraph -> ( ( F ( Paths ` G ) P /\ ( # ` F ) = 2 ) <-> ( F : ( 0 ..^ 2 ) -1-1-> dom I /\ P : ( 0 ... 2 ) -1-1-> V /\ E. x e. V E. y e. ( V \ { x } ) E. z e. ( V \ { x , y } ) ( ( ( P ` 0 ) = x /\ ( P ` 1 ) = z /\ ( P ` 2 ) = y ) /\ ( ( I ` ( F ` 0 ) ) = { x , z } /\ ( I ` ( F ` 1 ) ) = { z , y } ) ) ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    cP
    cG
    cpths
    cfv
    wbr
    cF
    chash
    cfv
    c2
    wceq
    wa
    cc0
    c2
    cfzo
    co
    cI
    cdm
    cF
    wf1
    #
    cc0
    c2
    cfz
    co
    cV
    cP
    wf1
    #
    cc0
    cP
    cfv
    vx
    cv
    #
    wceq
    c1
    cP
    cfv
    vz
    cv
    #
    wceq
    c2
    cP
    cfv
    vy
    cv
    #
    wceq
    w3a
    cc0
    cF
    cfv
    cI
    cfv
    @3
    @4
    cpr
    #
    wceq
    c1
    cF
    cfv
    cI
    cfv
    @4
    @5
    cpr
    wceq
    wa
    wa
    #
    vy
    cV
    @6
    cdif
    #
    wrex
    #
    vz
    cV
    @3
    csn
    cdif
    #
    wrex
    #
    vx
    cV
    wrex
    #
    w3a
    @1
    @2
    @7
    vz
    cV
    @3
    @5
    cpr
    cdif
    #
    wrex
    #
    vy
    @10
    wrex
    #
    vx
    cV
    wrex
    #
    w3a
    vx
    vz
    vy
    cP
    cF
    cG
    cI
    cV
    usgr2pthlem.v
    usgr2pthlem.i
    usgr2pth
    @0
    @12
    @16
    @1
    @2
    @0
    @11
    @15
    vx
    cV
    @11
    @15
    wb
    @0
    @3
    cV
    wcel
    wa
    @4
    @3
    wne
    #
    @9
    wa
    #
    vz
    cV
    wrex
    #
    @5
    @3
    wne
    #
    @14
    wa
    #
    vy
    cV
    wrex
    #
    @11
    @15
    @19
    @20
    @5
    @4
    wne
    #
    @17
    @7
    wa
    #
    w3a
    #
    vy
    cV
    wrex
    #
    vz
    cV
    wrex
    @25
    vz
    cV
    wrex
    #
    vy
    cV
    wrex
    @22
    @18
    @26
    vz
    cV
    @18
    @24
    vy
    @8
    wrex
    @26
    @17
    @7
    vy
    @8
    r19.42v
    @24
    vy
    cV
    @3
    @4
    rexdifpr
    bitr3i
    rexbii
    @25
    vz
    vy
    cV
    cV
    rexcom
    @27
    @21
    vy
    cV
    @27
    @17
    @4
    @5
    wne
    #
    @20
    @7
    wa
    #
    w3a
    #
    vz
    cV
    wrex
    @29
    vz
    @13
    wrex
    @21
    @25
    @30
    vz
    cV
    @25
    @20
    @23
    wa
    #
    @24
    wa
    @31
    @17
    wa
    #
    @7
    wa
    #
    @30
    @20
    @23
    @24
    df-3an
    @31
    @17
    @7
    anass
    @17
    @28
    wa
    #
    @20
    wa
    #
    @7
    wa
    @34
    @29
    wa
    @33
    @30
    @34
    @20
    @7
    anass
    @32
    @35
    @7
    @32
    @20
    @23
    @17
    wa
    #
    wa
    @36
    @20
    wa
    @35
    @20
    @23
    @17
    anass
    @20
    @36
    ancom
    @36
    @34
    @20
    @23
    @28
    @17
    @5
    @4
    necom
    anbi2ci
    anbi1i
    3bitri
    anbi1i
    @17
    @28
    @29
    df-3an
    3bitr4i
    3bitr2i
    rexbii
    @29
    vz
    cV
    @3
    @5
    rexdifpr
    @20
    @7
    vz
    @13
    r19.42v
    3bitr2i
    rexbii
    3bitri
    @9
    vz
    cV
    @3
    rexdifsn
    @14
    vy
    cV
    @3
    rexdifsn
    3bitr4i
    a1i
    rexbidva
    3anbi3d
    bitrd
end
