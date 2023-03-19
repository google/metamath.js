include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "c-bnj18.mm"
include "cv.mm"
include "wfn.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "csuc.mm"
include "ciun.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cab.mm"
include "cdm.mm"
include "cvv.mm"
include "biid.mm"
include "eqid.mm"
include "bnj882.mm"
include "wsbc.mm"
include "vex.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sbcie.mm"
include "bicomi.mm"
include "iuneq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "bnj873.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "rexbii2.mm"
include "abbii.mm"
include "df-iun.mm"
include "3eqtr4i.mm"
include "bnj849.mm"
include "dmex.mm"
include "fvex.mm"
include "iunex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "syl5eqel.mm"

theorem bnj893
  let cA: class A
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z


  assert |- ( ( R _FrSe A /\ X e. A ) -> _trCl ( X , A , R ) e. _V )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    cA
    cR
    cX
    c-bnj18
    vf
    vf
    cv
    #
    vn
    cv
    #
    wfn
    c0
    @3
    cfv
    #
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    vi
    cv
    #
    csuc
    #
    @4
    wcel
    #
    @9
    @3
    cfv
    #
    vy
    @8
    @3
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    w3a
    vn
    com
    c0
    csn
    cdif
    #
    wrex
    vf
    cab
    #
    vi
    @3
    cdm
    #
    @12
    ciun
    #
    ciun
    #
    cvv
    @7
    @17
    vy
    cA
    @19
    @18
    cR
    vf
    vi
    vn
    cX
    @7
    biid
    @17
    biid
    @18
    eqid
    #
    @19
    eqid
    #
    bnj882
    @2
    @22
    vf
    vg
    cv
    #
    @4
    wfn
    c0
    @25
    cfv
    #
    @6
    wceq
    #
    @10
    @9
    @25
    cfv
    #
    vy
    @8
    @25
    cfv
    #
    @13
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    w3a
    #
    vn
    @18
    wrex
    vg
    cab
    #
    @21
    ciun
    #
    cvv
    vw
    cv
    @21
    wcel
    #
    vf
    @19
    wrex
    #
    vw
    cab
    @37
    vf
    @35
    wrex
    #
    vw
    cab
    @22
    @36
    @38
    @39
    vw
    @37
    @37
    vf
    @19
    @35
    @3
    @19
    wcel
    @3
    @35
    wcel
    @37
    @19
    @35
    @3
    @7
    @17
    @19
    @18
    vf
    vg
    vn
    @27
    @33
    @24
    @7
    vf
    @25
    wsbc
    @27
    @7
    @27
    vf
    @25
    vg
    vex
    #
    vf
    vg
    weq
    #
    @5
    @26
    @6
    c0
    @3
    @25
    fveq1
    eqeq1d
    sbcie
    bicomi
    @17
    vf
    @25
    wsbc
    @33
    @17
    @33
    vf
    @25
    @40
    @41
    @16
    @32
    vi
    com
    @41
    @15
    @31
    @10
    @41
    @11
    @28
    @14
    @30
    @9
    @3
    @25
    fveq1
    @41
    vy
    @12
    @29
    @13
    @8
    @3
    @25
    fveq1
    iuneq1d
    eqeq12d
    imbi2d
    ralbidv
    sbcie
    bicomi
    bnj873
    eleq2i
    anbi1i
    rexbii2
    abbii
    vf
    vw
    @19
    @21
    df-iun
    vf
    vw
    @35
    @21
    df-iun
    3eqtr4i
    @2
    @35
    cvv
    wcel
    @21
    cvv
    wcel
    #
    vf
    @35
    wral
    @36
    cvv
    wcel
    @27
    @33
    @0
    @1
    @4
    @18
    wcel
    w3a
    #
    @34
    @2
    vy
    cA
    @35
    @18
    cR
    vg
    vz
    vi
    vn
    cX
    @27
    vg
    vz
    cv
    #
    wsbc
    #
    @33
    vg
    @44
    wsbc
    #
    @34
    vg
    @44
    wsbc
    #
    @27
    biid
    @33
    biid
    @23
    @35
    eqid
    @43
    biid
    @34
    biid
    @45
    biid
    @46
    biid
    @47
    biid
    @2
    biid
    bnj849
    @42
    vf
    @35
    vi
    @20
    @12
    @3
    vf
    vex
    dmex
    @8
    @3
    fvex
    iunex
    rgenw
    vf
    @35
    @21
    cvv
    cvv
    iunexg
    sylancl
    syl5eqel
    syl5eqel
end
