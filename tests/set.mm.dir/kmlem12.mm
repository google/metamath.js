include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wcel.mm"
include "weu.mm"
include "wi.mm"
include "wceq.mm"
include "difeq1.mm"
include "sneq.mm"
include "difeq2d.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "neeq1d.mm"
include "cbvralv.mm"
include "ineq1d.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "imbi12i.mm"
include "in12.mm"
include "incom.mm"
include "eqtri.mm"
include "kmlem11.mm"
include "syl5req.mm"
include "ax-1.mm"
include "syl6bi.mm"
include "ralimia.mm"
include "imim2i.mm"
include "sylbi.mm"
include "wrex.mm"
include "cab.mm"
include "wal.mm"
include "raleqi.mm"
include "df-ral.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "imbi1i.mm"
include "r19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "ralcom4.mm"
include "difexi.mm"
include "neeq1.mm"
include "ineq1.mm"
include "imbi12d.mm"
include "ceqsalv.mm"
include "ralbii.mm"
include "3bitr2i.mm"
include "3bitri.mm"
include "ralim.mm"
include "syl11.mm"

theorem kmlem12
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vw: setvar w
  let vh: setvar h
  let vg: setvar g
  let wph: wff ph
  assume kmlem9.1: |- A = { u | E. t e. x u = ( t \ U. ( x \ { t } ) ) }

  disjoint x y
  disjoint x z
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint y z
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint u v
  disjoint t v
  disjoint t u
  disjoint A y
  disjoint A z
  disjoint A v
  disjoint w x
  disjoint h x
  disjoint g x
  disjoint w y
  disjoint h y
  disjoint g y
  disjoint w z
  disjoint h z
  disjoint g z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint g w
  disjoint h v
  disjoint g v
  disjoint h u
  disjoint g u
  disjoint h t
  disjoint g t
  disjoint g h
  disjoint A w
  disjoint A h
  disjoint A g
  disjoint h ph
  assert |- ( A. z e. x ( z \ U. ( x \ { z } ) ) =/= (/) -> ( A. z e. A ( z =/= (/) -> E! v v e. ( z i^i y ) ) -> A. z e. x ( z =/= (/) -> E! v v e. ( z i^i ( y i^i U. A ) ) ) ) )

  proof
    vt
    cv
    #
    vx
    cv
    #
    @0
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    c0
    wne
    #
    vt
    @1
    wral
    #
    vv
    cv
    #
    @5
    vy
    cv
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    vt
    @1
    wral
    #
    wi
    #
    vz
    cv
    #
    @1
    @15
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    c0
    wne
    #
    vz
    @1
    wral
    #
    @15
    c0
    wne
    #
    @8
    @15
    @9
    cA
    cuni
    #
    cin
    cin
    #
    wcel
    #
    vv
    weu
    #
    wi
    #
    vz
    @1
    wral
    #
    @22
    @8
    @15
    @9
    cin
    #
    wcel
    #
    vv
    weu
    #
    wi
    #
    vz
    cA
    wral
    #
    @14
    @21
    @8
    @19
    @9
    cin
    #
    wcel
    #
    vv
    weu
    #
    vz
    @1
    wral
    #
    wi
    @21
    @28
    wi
    @7
    @21
    @13
    @37
    @6
    @20
    vt
    vz
    @1
    @0
    @15
    wceq
    #
    @5
    @19
    c0
    @38
    @5
    @15
    @4
    cdif
    @19
    @0
    @15
    @4
    difeq1
    @38
    @4
    @18
    @15
    @38
    @3
    @17
    @38
    @2
    @16
    @1
    @0
    @15
    sneq
    difeq2d
    unieqd
    difeq2d
    eqtrd
    #
    neeq1d
    cbvralv
    @12
    @36
    vt
    vz
    @1
    @38
    @11
    @35
    vv
    @38
    @10
    @34
    @8
    @38
    @5
    @19
    @9
    @39
    ineq1d
    eleq2d
    eubidv
    cbvralv
    imbi12i
    @37
    @28
    @21
    @36
    @27
    vz
    @1
    @15
    @1
    wcel
    #
    @36
    @26
    @27
    @40
    @35
    @25
    vv
    @40
    @34
    @24
    @8
    @40
    @24
    @15
    @23
    cin
    #
    @9
    cin
    #
    @34
    @24
    @9
    @41
    cin
    @42
    @15
    @9
    @23
    in12
    @9
    @41
    incom
    eqtri
    @40
    @41
    @19
    @9
    vx
    vz
    vu
    vt
    cA
    kmlem9.1
    kmlem11
    ineq1d
    syl5req
    eleq2d
    eubidv
    @26
    @22
    ax-1
    syl6bi
    ralimia
    imim2i
    sylbi
    @33
    @6
    @12
    wi
    #
    vt
    @1
    wral
    #
    @14
    @33
    @32
    vz
    vu
    cv
    #
    @5
    wceq
    #
    vt
    @1
    wrex
    #
    vu
    cab
    #
    wral
    @15
    @48
    wcel
    #
    @32
    wi
    #
    vz
    wal
    #
    @44
    @32
    vz
    cA
    @48
    kmlem9.1
    raleqi
    @32
    vz
    @48
    df-ral
    @51
    @15
    @5
    wceq
    #
    @32
    wi
    #
    vt
    @1
    wral
    #
    vz
    wal
    @53
    vz
    wal
    #
    vt
    @1
    wral
    @44
    @50
    @54
    vz
    @50
    @52
    vt
    @1
    wrex
    #
    @32
    wi
    @54
    @49
    @56
    @32
    @47
    @56
    vu
    @15
    vz
    vex
    @45
    @15
    wceq
    @46
    @52
    vt
    @1
    @45
    @15
    @5
    eqeq1
    rexbidv
    elab
    imbi1i
    @52
    @32
    vt
    @1
    r19.23v
    bitr4i
    albii
    @53
    vt
    vz
    @1
    ralcom4
    @55
    @43
    vt
    @1
    @32
    @43
    vz
    @5
    @0
    @4
    vt
    vex
    difexi
    @52
    @22
    @6
    @31
    @12
    @15
    @5
    c0
    neeq1
    @52
    @30
    @11
    vv
    @52
    @29
    @10
    @8
    @15
    @5
    @9
    ineq1
    eleq2d
    eubidv
    imbi12d
    ceqsalv
    ralbii
    3bitr2i
    3bitri
    @6
    @12
    vt
    @1
    ralim
    sylbi
    syl11
end
