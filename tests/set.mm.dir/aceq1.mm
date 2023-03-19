include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "biidd.mm"
include "cbvralv.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvreuv.mm"
include "ralbii.mm"
include "bitri.mm"
include "anbi1d.mm"
include "reueqd.mm"
include "raleqbi1dv.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "19.21v.mm"
include "impexp.mm"
include "bi2.04.mm"
include "albii.mm"
include "weu.mm"
include "df-eu.mm"
include "df-reu.mm"
include "19.42v.mm"
include "an42.mm"
include "anass.mm"
include "bitr3i.mm"
include "df-rex.mm"
include "elequ2.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "anbi2i.mm"
include "bibi1i.mm"
include "imbi2i.mm"
include "df-ral.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfex.mm"
include "nfim.mm"
include "imbi1d.mm"
include "cbval.mm"
include "alcom.mm"
include "3bitr4ri.mm"

theorem aceq1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let vh: setvar h

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint t x
  disjoint h x
  disjoint t y
  disjoint h y
  disjoint t z
  disjoint h z
  disjoint t w
  disjoint h w
  disjoint t v
  disjoint h v
  disjoint t u
  disjoint h u
  disjoint h t
  assert |- ( E. y A. z e. x A. w e. z E! v e. z E. u e. y ( z e. u /\ v e. u ) <-> E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. x A. z ( E. x ( ( z e. w /\ w e. x ) /\ ( z e. x /\ x e. y ) ) <-> z = x ) ) )

  proof
    vz
    vu
    wel
    #
    vv
    vu
    wel
    #
    wa
    #
    vu
    vy
    cv
    #
    wrex
    #
    vv
    vz
    cv
    #
    wreu
    #
    vw
    @5
    wral
    #
    vz
    vx
    cv
    #
    wral
    #
    vy
    wex
    vw
    vu
    wel
    #
    @0
    wa
    #
    vu
    @3
    wrex
    #
    vz
    vw
    cv
    #
    wreu
    #
    vt
    @13
    wral
    #
    vw
    @8
    wral
    #
    vy
    wex
    vz
    vw
    wel
    #
    vw
    vx
    wel
    #
    wa
    #
    @19
    vz
    vx
    wel
    #
    vx
    vy
    wel
    #
    wa
    wa
    #
    vx
    wex
    #
    vz
    vx
    weq
    #
    wb
    #
    vz
    wal
    #
    vx
    wex
    #
    wi
    #
    vw
    wal
    vz
    wal
    #
    vy
    wex
    @9
    @16
    vy
    vh
    vu
    wel
    #
    @1
    wa
    #
    vu
    @3
    wrex
    #
    vv
    vh
    cv
    #
    wreu
    #
    vw
    @33
    wral
    #
    vh
    @8
    wral
    @30
    @0
    wa
    #
    vu
    @3
    wrex
    #
    vz
    @33
    wreu
    #
    vt
    @33
    wral
    #
    vh
    @8
    wral
    @9
    @16
    @35
    @39
    vh
    @8
    @35
    @34
    vt
    @33
    wral
    @39
    @34
    @34
    vw
    vt
    @33
    vw
    vt
    weq
    @34
    biidd
    cbvralv
    @34
    @38
    vt
    @33
    @32
    @37
    vv
    vz
    @33
    vv
    vz
    weq
    #
    @31
    @36
    vu
    @3
    @40
    @1
    @0
    @30
    vv
    cv
    @5
    vu
    cv
    #
    eleq1
    anbi2d
    rexbidv
    cbvreuv
    ralbii
    bitri
    ralbii
    @7
    @35
    vz
    vh
    @8
    @6
    @34
    vw
    @5
    @33
    @4
    @32
    vv
    @5
    @33
    vz
    vh
    weq
    #
    @2
    @31
    vu
    @3
    @42
    @0
    @30
    @1
    @5
    @33
    @41
    eleq1
    anbi1d
    rexbidv
    reueqd
    raleqbi1dv
    cbvralv
    @15
    @39
    vw
    vh
    @8
    @14
    @38
    vt
    @13
    @33
    @12
    @37
    vz
    @13
    @33
    vw
    vh
    weq
    #
    @11
    @36
    vu
    @3
    @43
    @10
    @30
    @0
    @13
    @33
    @41
    eleq1
    anbi1d
    rexbidv
    reueqd
    raleqbi1dv
    cbvralv
    3bitr4i
    exbii
    @16
    @29
    vy
    @28
    vz
    wal
    #
    vw
    wal
    @18
    @15
    wi
    #
    vw
    wal
    @29
    @16
    @44
    @45
    vw
    @18
    @17
    @27
    wi
    #
    wi
    #
    vz
    wal
    @18
    @46
    vz
    wal
    #
    wi
    @44
    @45
    @18
    @46
    vz
    19.21v
    @28
    @47
    vz
    @28
    @17
    @18
    @27
    wi
    wi
    @47
    @17
    @18
    @27
    impexp
    @17
    @18
    @27
    bi2.04
    bitri
    albii
    @15
    @48
    @18
    vt
    vw
    wel
    #
    @14
    wi
    #
    vt
    wal
    @49
    @27
    wi
    #
    vt
    wal
    @15
    @48
    @50
    @51
    vt
    @14
    @27
    @49
    @17
    @12
    wa
    #
    vz
    weu
    @52
    @24
    wb
    #
    vz
    wal
    #
    vx
    wex
    @14
    @27
    @52
    vz
    vx
    df-eu
    @12
    vz
    @13
    df-reu
    @26
    @54
    vx
    @25
    @53
    vz
    @23
    @52
    @24
    @17
    @21
    @18
    @20
    wa
    #
    wa
    #
    wa
    #
    vx
    wex
    @17
    @56
    vx
    wex
    #
    wa
    @23
    @52
    @17
    @56
    vx
    19.42v
    @22
    @57
    vx
    @22
    @17
    @21
    wa
    @55
    wa
    @57
    @17
    @21
    @18
    @20
    an42
    @17
    @21
    @55
    anass
    bitr3i
    exbii
    @12
    @58
    @17
    @12
    vu
    vy
    wel
    #
    @11
    wa
    #
    vu
    wex
    @58
    @11
    vu
    @3
    df-rex
    @60
    @56
    vu
    vx
    vu
    vx
    weq
    #
    @59
    @21
    @11
    @55
    @41
    @8
    @3
    eleq1
    @61
    @10
    @18
    @0
    @20
    vu
    vx
    vw
    elequ2
    vu
    vx
    vz
    elequ2
    anbi12d
    anbi12d
    cbvexv
    bitri
    anbi2i
    3bitr4i
    bibi1i
    albii
    exbii
    3bitr4i
    imbi2i
    albii
    @14
    vt
    @13
    df-ral
    @46
    @51
    vz
    vt
    @46
    vt
    nfv
    @49
    @27
    vz
    @49
    vz
    nfv
    @26
    vz
    vx
    @25
    vz
    nfa1
    nfex
    nfim
    vz
    vt
    weq
    @17
    @49
    @27
    @5
    vt
    cv
    @13
    eleq1
    imbi1d
    cbval
    3bitr4i
    imbi2i
    3bitr4i
    albii
    @28
    vz
    vw
    alcom
    @15
    vw
    @8
    df-ral
    3bitr4ri
    exbii
    bitri
end
