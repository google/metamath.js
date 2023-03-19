include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "wss.mm"
include "cdm.mm"
include "wfn.mm"
include "wa.mm"
include "crn.mm"
include "cpw.mm"
include "vex.mm"
include "rnex.mm"
include "pwex.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "spcv.mm"
include "wbr.mm"
include "cab.mm"
include "copab.mm"
include "cmpt.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "eldm.mm"
include "abn0.mm"
include "bitr4i.mm"
include "brelrn.mm"
include "abssi.mm"
include "elpw2.mm"
include "mpbir.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5bi.mm"
include "imp.mm"
include "fvex.mm"
include "breq2.mm"
include "cbvabv.mm"
include "elab2.mm"
include "sylib.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "ssopab2dv.mm"
include "opabss.mm"
include "syl6ss.mm"
include "syl5eqss.mm"
include "fnmpti.mm"
include "cvv.mm"
include "ssex.mm"
include "adantr.mm"
include "sseq1.mm"
include "fneq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpcom.mm"
include "sylancl.mm"
include "exlimiv.mm"
include "syl.mm"
include "cbvexv.mm"

theorem aceq3lem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vf: setvar f
  let cF: class F
  let vh: setvar h
  let vg: setvar g
  assume aceq3lem.1: |- F = ( w e. dom y |-> ( f ` { u | w y u } ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint u x
  disjoint f x
  disjoint y z
  disjoint w y
  disjoint u y
  disjoint f y
  disjoint w z
  disjoint u z
  disjoint f z
  disjoint u w
  disjoint f w
  disjoint f u
  disjoint h x
  disjoint g x
  disjoint h y
  disjoint g y
  disjoint h z
  disjoint g z
  disjoint h w
  disjoint g w
  disjoint h u
  disjoint g u
  disjoint g h
  disjoint f h
  disjoint f g
  disjoint F h
  disjoint F g
  assert |- ( A. x E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) -> E. f ( f C_ y /\ f Fn dom y ) )

  proof
    vz
    cv
    #
    c0
    wne
    #
    @0
    vf
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    vx
    cv
    #
    wral
    #
    vf
    wex
    #
    vx
    wal
    #
    vg
    cv
    #
    vy
    cv
    #
    wss
    #
    @10
    @11
    cdm
    #
    wfn
    #
    wa
    #
    vg
    wex
    #
    @2
    @11
    wss
    #
    @2
    @13
    wfn
    #
    wa
    #
    vf
    wex
    @9
    @5
    vz
    @11
    crn
    #
    cpw
    #
    wral
    #
    vf
    wex
    #
    @16
    @8
    @23
    vx
    @21
    @20
    @11
    vy
    vex
    #
    rnex
    #
    pwex
    @6
    @21
    wceq
    @7
    @22
    vf
    @5
    vz
    @6
    @21
    raleq
    exbidv
    spcv
    @22
    @16
    vf
    @22
    cF
    @11
    wss
    #
    cF
    @13
    wfn
    #
    @16
    @22
    cF
    vw
    cv
    #
    @13
    wcel
    #
    vh
    cv
    #
    @28
    vu
    cv
    #
    @11
    wbr
    #
    vu
    cab
    #
    @2
    cfv
    #
    wceq
    #
    wa
    #
    vw
    vh
    copab
    #
    @11
    cF
    vw
    @13
    @34
    cmpt
    @37
    aceq3lem.1
    vw
    vh
    @13
    @34
    df-mpt
    eqtri
    @22
    @37
    @28
    @30
    @11
    wbr
    #
    vw
    vh
    copab
    @11
    @22
    @36
    @38
    vw
    vh
    @22
    @29
    @35
    @38
    @22
    @29
    wa
    #
    @38
    @35
    @28
    @34
    @11
    wbr
    #
    @39
    @34
    @33
    wcel
    #
    @40
    @22
    @29
    @41
    @29
    @33
    c0
    wne
    #
    @22
    @41
    @29
    @32
    vu
    wex
    @42
    vu
    @28
    @11
    vw
    vex
    #
    eldm
    @32
    vu
    abn0
    bitr4i
    @33
    @21
    wcel
    #
    @22
    @42
    @41
    wi
    #
    wi
    @44
    @33
    @20
    wss
    @32
    vu
    @20
    @28
    @31
    @11
    @43
    vu
    vex
    brelrn
    abssi
    @33
    @20
    @25
    elpw2
    mpbir
    @5
    @45
    vz
    @33
    @21
    @0
    @33
    wceq
    #
    @1
    @42
    @4
    @41
    @0
    @33
    c0
    neeq1
    @46
    @3
    @34
    @0
    @33
    @0
    @33
    @2
    fveq2
    @46
    id
    eleq12d
    imbi12d
    rspcv
    ax-mp
    syl5bi
    imp
    @28
    @0
    @11
    wbr
    #
    @40
    vz
    @34
    @33
    @33
    @2
    fvex
    #
    @0
    @34
    @28
    @11
    breq2
    @32
    @47
    vu
    vz
    @31
    @0
    @28
    @11
    breq2
    cbvabv
    elab2
    sylib
    @30
    @34
    @28
    @11
    breq2
    syl5ibrcom
    expimpd
    ssopab2dv
    vw
    vh
    @11
    opabss
    syl6ss
    syl5eqss
    vw
    @13
    @34
    cF
    @48
    aceq3lem.1
    fnmpti
    cF
    cvv
    wcel
    #
    @26
    @27
    wa
    #
    @16
    @26
    @49
    @27
    cF
    @11
    @24
    ssex
    adantr
    @15
    @50
    vg
    cF
    cvv
    @10
    cF
    wceq
    @12
    @26
    @14
    @27
    @10
    cF
    @11
    sseq1
    @13
    @10
    cF
    fneq1
    anbi12d
    spcegv
    mpcom
    sylancl
    exlimiv
    syl
    @15
    @19
    vg
    vf
    @10
    @2
    wceq
    @12
    @17
    @14
    @18
    @10
    @2
    @11
    sseq1
    @13
    @10
    @2
    fneq1
    anbi12d
    cbvexv
    sylib
end
