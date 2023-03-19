include "wel.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "cdif.mm"
include "cdom.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "weq.mm"
include "wb.mm"
include "axgroth4.mm"
include "3anass.mm"
include "dfss2.mm"
include "elin.mm"
include "imbi12i.mm"
include "albii.mm"
include "rexbii.mm"
include "df-rex.mm"
include "bitri.mm"
include "ralbii.mm"
include "df-ral.mm"
include "cpr.mm"
include "wmo.mm"
include "cvv.mm"
include "vex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "c0.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "brdom6disj.mm"
include "orbi1i.mm"
include "19.44v.mm"
include "bitr4i.mm"
include "19.35.mm"
include "grothprimlem.mm"
include "mobii.mm"
include "mo2v.mm"
include "wn.mm"
include "eldif.mm"
include "pm5.6.mm"
include "anbi12i.mm"
include "19.26.mm"
include "imbi2i.mm"
include "exbii.mm"
include "anbi2i.mm"
include "mpbi.mm"

theorem grothprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let vg: setvar g
  let vh: setvar h

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint g x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint g y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint g z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint g w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint g v
  disjoint t u
  disjoint h u
  disjoint g u
  disjoint h t
  disjoint g t
  disjoint g h
  assert |- E. y ( x e. y /\ A. z ( ( z e. y -> E. v ( v e. y /\ A. w ( A. u ( u e. w -> u e. z ) -> ( w e. y /\ w e. v ) ) ) ) /\ E. w ( ( w e. z -> w e. y ) -> ( A. v ( ( v e. z -> E. t A. u ( E. g ( g e. w /\ A. h ( h e. g <-> ( h = v \/ h = u ) ) ) -> u = t ) ) /\ ( v e. y -> ( v e. z \/ E. u ( u e. z /\ E. g ( g e. w /\ A. h ( h e. g <-> ( h = u \/ h = v ) ) ) ) ) ) ) \/ z e. y ) ) ) )

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
    @1
    vy
    cv
    #
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
    @4
    wrex
    #
    vz
    @4
    wral
    #
    @2
    @4
    wss
    #
    @4
    @2
    cdif
    #
    @2
    cdom
    wbr
    #
    vz
    vy
    wel
    #
    wo
    #
    wi
    #
    vz
    wal
    #
    w3a
    #
    vy
    wex
    @0
    @14
    vv
    vy
    wel
    #
    vu
    vw
    wel
    vu
    vz
    wel
    #
    wi
    vu
    wal
    #
    vw
    vy
    wel
    #
    vw
    vv
    wel
    wa
    #
    wi
    #
    vw
    wal
    #
    wa
    vv
    wex
    #
    wi
    #
    vw
    vz
    wel
    @22
    wi
    #
    vv
    vz
    wel
    #
    vg
    vw
    wel
    #
    vh
    vg
    wel
    #
    vh
    vv
    weq
    #
    vh
    vu
    weq
    #
    wo
    wb
    vh
    wal
    wa
    vg
    wex
    #
    vu
    vt
    weq
    wi
    vu
    wal
    vt
    wex
    #
    wi
    #
    @19
    @29
    @20
    @30
    @31
    @33
    @32
    wo
    wb
    vh
    wal
    wa
    vg
    wex
    #
    wa
    vu
    wex
    #
    wo
    wi
    #
    wa
    vv
    wal
    #
    @14
    wo
    #
    wi
    #
    vw
    wex
    #
    wa
    vz
    wal
    #
    wa
    #
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    axgroth4
    @18
    @45
    vy
    @18
    @0
    @10
    @17
    wa
    #
    wa
    @45
    @0
    @10
    @17
    3anass
    @46
    @44
    @0
    @46
    @27
    vz
    wal
    #
    @43
    vz
    wal
    #
    wa
    @44
    @10
    @47
    @17
    @48
    @10
    @26
    vz
    @4
    wral
    @47
    @9
    @26
    vz
    @4
    @9
    @25
    vv
    @4
    wrex
    @26
    @8
    @25
    vv
    @4
    @7
    @24
    vw
    @3
    @21
    @6
    @23
    vu
    @1
    @2
    dfss2
    @1
    @4
    @5
    elin
    imbi12i
    albii
    rexbii
    @25
    vv
    @4
    df-rex
    bitri
    ralbii
    @26
    vz
    @4
    df-ral
    bitri
    @16
    @43
    vz
    @16
    @28
    @5
    vu
    cv
    #
    cpr
    @1
    wcel
    #
    vu
    wmo
    #
    vv
    @2
    wral
    #
    @49
    @5
    cpr
    @1
    wcel
    #
    vu
    @2
    wrex
    #
    vv
    @12
    wral
    #
    wa
    #
    @14
    wo
    #
    wi
    #
    vw
    wex
    #
    @43
    @16
    @28
    vw
    wal
    #
    @57
    vw
    wex
    #
    wi
    @59
    @11
    @60
    @15
    @61
    vw
    @2
    @4
    dfss2
    @15
    @56
    vw
    wex
    #
    @14
    wo
    @61
    @13
    @62
    @14
    vv
    vu
    @12
    @2
    vw
    @4
    cvv
    wcel
    @12
    cvv
    wcel
    vy
    vex
    @4
    @2
    cvv
    difexg
    ax-mp
    vz
    vex
    @12
    @2
    cin
    @2
    @12
    cin
    c0
    @12
    @2
    incom
    @2
    @4
    disjdif
    eqtri
    brdom6disj
    orbi1i
    @56
    @14
    vw
    19.44v
    bitr4i
    imbi12i
    @28
    @57
    vw
    19.35
    bitr4i
    @58
    @42
    vw
    @57
    @41
    @28
    @56
    @40
    @14
    @56
    @36
    vv
    wal
    #
    @39
    vv
    wal
    #
    wa
    @40
    @52
    @63
    @55
    @64
    @52
    @35
    vv
    @2
    wral
    @63
    @51
    @35
    vv
    @2
    @51
    @34
    vu
    wmo
    @35
    @50
    @34
    vu
    vw
    vu
    vv
    vg
    vh
    grothprimlem
    mobii
    @34
    vu
    vt
    mo2v
    bitri
    ralbii
    @35
    vv
    @2
    df-ral
    bitri
    @55
    @5
    @12
    wcel
    #
    @54
    wi
    #
    vv
    wal
    @64
    @54
    vv
    @12
    df-ral
    @66
    @39
    vv
    @66
    @19
    @29
    wn
    wa
    #
    @38
    wi
    @39
    @65
    @67
    @54
    @38
    @5
    @4
    @2
    eldif
    @54
    @37
    vu
    @2
    wrex
    @38
    @53
    @37
    vu
    @2
    vw
    vv
    vu
    vg
    vh
    grothprimlem
    rexbii
    @37
    vu
    @2
    df-rex
    bitri
    imbi12i
    @19
    @29
    @38
    pm5.6
    bitri
    albii
    bitri
    anbi12i
    @36
    @39
    vv
    19.26
    bitr4i
    orbi1i
    imbi2i
    exbii
    bitri
    albii
    anbi12i
    @27
    @43
    vz
    19.26
    bitr4i
    anbi2i
    bitri
    exbii
    mpbi
end
