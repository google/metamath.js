include "cv.mm"
include "wne.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wel.mm"
include "wex.mm"
include "wal.mm"
include "weq.mm"
include "neeq1.mm"
include "ineq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "cbvrexv.mm"
include "df-rex.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "cbvralv.mm"
include "df-ral.mm"
include "bitri.mm"
include "anbi2i.mm"
include "19.28v.mm"
include "neeq2.mm"
include "ineq2.mm"
include "imbi2i.mm"
include "19.37v.mm"
include "bitr4i.mm"
include "19.42v.mm"
include "19.3v.mm"
include "elin.mm"
include "baibr.mm"
include "anass.mm"
include "syl6bb.mm"
include "pm5.74i.mm"
include "bitr2i.mm"
include "exbii.mm"
include "3bitr2i.mm"
include "albii.mm"
include "3bitri.mm"

theorem kmlem14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assume kmlem14.1: |- ( ph <-> ( z e. y -> ( ( v e. x /\ y =/= v ) /\ z e. v ) ) )
  assume kmlem14.2: |- ( ps <-> ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) )
  assume kmlem14.3: |- ( ch <-> A. z e. x E! v v e. ( z i^i y ) )

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
  disjoint ph u
  assert |- ( E. z e. x A. v e. z E. w e. x ( z =/= w /\ v e. ( z i^i w ) ) <-> E. y A. z E. v A. u ( y e. x /\ ph ) )

  proof
    vz
    cv
    #
    vw
    cv
    #
    wne
    #
    vv
    cv
    #
    @0
    @1
    cin
    #
    wcel
    #
    wa
    #
    vw
    vx
    cv
    #
    wrex
    #
    vv
    @0
    wral
    #
    vz
    @7
    wrex
    vy
    cv
    #
    @1
    wne
    #
    @3
    @10
    @1
    cin
    #
    wcel
    #
    wa
    #
    vw
    @7
    wrex
    #
    vv
    @10
    wral
    #
    vy
    @7
    wrex
    vy
    vx
    wel
    #
    @16
    wa
    #
    vy
    wex
    @17
    wph
    wa
    #
    vu
    wal
    #
    vv
    wex
    #
    vz
    wal
    #
    vy
    wex
    @9
    @16
    vz
    vy
    @7
    @8
    @15
    vv
    @0
    @10
    vz
    vy
    weq
    #
    @6
    @14
    vw
    @7
    @23
    @2
    @11
    @5
    @13
    @0
    @10
    @1
    neeq1
    @23
    @4
    @12
    @3
    @0
    @10
    @1
    ineq1
    eleq2d
    anbi12d
    rexbidv
    raleqbi1dv
    cbvrexv
    @16
    vy
    @7
    df-rex
    @18
    @22
    vy
    @18
    @17
    vz
    vy
    wel
    #
    @11
    @0
    @12
    wcel
    #
    wa
    #
    vw
    @7
    wrex
    #
    wi
    #
    vz
    wal
    #
    wa
    @17
    @28
    wa
    #
    vz
    wal
    @22
    @16
    @29
    @17
    @16
    @27
    vz
    @10
    wral
    @29
    @15
    @27
    vv
    vz
    @10
    vv
    vz
    weq
    #
    @14
    @26
    vw
    @7
    @31
    @13
    @25
    @11
    @3
    @0
    @12
    eleq1
    anbi2d
    rexbidv
    cbvralv
    @27
    vz
    @10
    df-ral
    bitri
    anbi2i
    @17
    @28
    vz
    19.28v
    @30
    @21
    vz
    @30
    @17
    @24
    vv
    vx
    wel
    #
    @10
    @3
    wne
    #
    @0
    @10
    @3
    cin
    #
    wcel
    #
    wa
    #
    wa
    #
    wi
    #
    vv
    wex
    #
    wa
    @17
    @38
    wa
    #
    vv
    wex
    @21
    @28
    @39
    @17
    @28
    @24
    @37
    vv
    wex
    #
    wi
    @39
    @27
    @41
    @24
    @27
    @36
    vv
    @7
    wrex
    @41
    @26
    @36
    vw
    vv
    @7
    vw
    vv
    weq
    #
    @11
    @33
    @25
    @35
    @1
    @3
    @10
    neeq2
    @42
    @12
    @34
    @0
    @1
    @3
    @10
    ineq2
    eleq2d
    anbi12d
    cbvrexv
    @36
    vv
    @7
    df-rex
    bitri
    imbi2i
    @24
    @37
    vv
    19.37v
    bitr4i
    anbi2i
    @17
    @38
    vv
    19.42v
    @40
    @20
    vv
    @20
    @19
    @40
    @19
    vu
    19.3v
    wph
    @38
    @17
    wph
    @24
    @32
    @33
    wa
    #
    vz
    vv
    wel
    #
    wa
    #
    wi
    @38
    kmlem14.1
    @24
    @45
    @37
    @24
    @45
    @43
    @35
    wa
    @37
    @24
    @44
    @35
    @43
    @35
    @24
    @44
    @0
    @10
    @3
    elin
    baibr
    anbi2d
    @32
    @33
    @35
    anass
    syl6bb
    pm5.74i
    bitri
    anbi2i
    bitr2i
    exbii
    3bitr2i
    albii
    3bitr2i
    exbii
    3bitri
end
