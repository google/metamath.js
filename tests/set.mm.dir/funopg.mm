include "wcel.mm"
include "cop.mm"
include "wfun.mm"
include "wceq.mm"
include "cv.mm"
include "weq.mm"
include "wi.mm"
include "opeq1.mm"
include "funeqd.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "opeq2.mm"
include "eqeq2.mm"
include "csn.mm"
include "cpr.mm"
include "wa.mm"
include "wex.mm"
include "wrel.mm"
include "funrel.mm"
include "vex.mm"
include "relop.mm"
include "sylib.mm"
include "opth.mm"
include "opid.mm"
include "preq1i.mm"
include "dfop.mm"
include "preq2i.mm"
include "snex.mm"
include "zfpair2.mm"
include "3eqtr4ri.mm"
include "eqeq2i.mm"
include "bitr3i.mm"
include "wal.mm"
include "dffun4.mm"
include "simprbi.mm"
include "opex.mm"
include "prid1.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "prid2.mm"
include "jca.mm"
include "cvv.mm"
include "w3a.mm"
include "opeq12.mm"
include "3adant3.mm"
include "eleq1d.mm"
include "3adant2.mm"
include "anbi12d.mm"
include "wb.mm"
include "eqeq12.mm"
include "3adant1.mm"
include "spc3gv.mm"
include "mp3an.mm"
include "syl2im.mm"
include "syl5bi.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5req.mm"
include "eqeq2d.mm"
include "eqtr3.mm"
include "expcom.mm"
include "syl6bi.mm"
include "com13.mm"
include "imp.mm"
include "sylcom.mm"
include "exlimdvv.mm"
include "mpd.mm"
include "vtocl2g.mm"
include "3impia.mm"

theorem funopg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. V /\ B e. W /\ Fun <. A , B >. ) -> A = B )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cA
    cB
    cop
    #
    wfun
    #
    cA
    cB
    wceq
    #
    vu
    cv
    #
    vt
    cv
    #
    cop
    #
    wfun
    #
    vu
    vt
    weq
    #
    wi
    cA
    @4
    cop
    #
    wfun
    #
    cA
    @4
    wceq
    #
    wi
    @1
    @2
    wi
    vu
    vt
    cA
    cB
    cV
    cW
    @3
    cA
    wceq
    #
    @6
    @9
    @7
    @10
    @11
    @5
    @8
    @3
    cA
    @4
    opeq1
    funeqd
    @3
    cA
    @4
    eqeq1
    imbi12d
    @4
    cB
    wceq
    #
    @9
    @1
    @10
    @2
    @12
    @8
    @0
    @4
    cB
    cA
    opeq2
    funeqd
    @4
    cB
    cA
    eqeq2
    imbi12d
    @6
    @3
    vx
    cv
    #
    csn
    #
    wceq
    #
    @4
    @13
    vy
    cv
    #
    cpr
    #
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @7
    @6
    @5
    wrel
    #
    @20
    @5
    funrel
    vx
    vy
    @3
    @4
    vu
    vex
    #
    vt
    vex
    #
    relop
    sylib
    @6
    @19
    @7
    vx
    vy
    @6
    @19
    vx
    vy
    weq
    #
    @7
    @19
    @5
    @13
    @13
    cop
    #
    @13
    @16
    cop
    #
    cpr
    #
    wceq
    #
    @6
    @24
    @19
    @5
    @14
    @17
    cop
    #
    wceq
    @28
    @3
    @4
    @14
    @17
    @22
    @23
    opth
    @29
    @27
    @5
    @25
    @14
    @17
    cpr
    #
    cpr
    @14
    csn
    #
    @30
    cpr
    @27
    @29
    @25
    @31
    @30
    @13
    vx
    vex
    #
    opid
    preq1i
    @26
    @30
    @25
    @13
    @16
    @32
    vy
    vex
    #
    dfop
    preq2i
    @14
    @17
    @13
    snex
    vx
    vy
    zfpair2
    dfop
    3eqtr4ri
    eqeq2i
    bitr3i
    @6
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @5
    wcel
    #
    @34
    vv
    cv
    #
    cop
    #
    @5
    wcel
    #
    wa
    #
    vw
    vv
    weq
    #
    wi
    #
    vv
    wal
    vw
    wal
    vz
    wal
    #
    @28
    @25
    @5
    wcel
    #
    @26
    @5
    wcel
    #
    wa
    #
    @24
    @6
    @21
    @44
    vz
    vw
    vv
    @5
    dffun4
    simprbi
    @28
    @45
    @46
    @28
    @45
    @25
    @27
    wcel
    @25
    @26
    @13
    @13
    opex
    prid1
    @5
    @27
    @25
    eleq2
    mpbiri
    @28
    @46
    @26
    @27
    wcel
    @25
    @26
    @13
    @16
    opex
    prid2
    @5
    @27
    @26
    eleq2
    mpbiri
    jca
    @13
    cvv
    wcel
    #
    @48
    @16
    cvv
    wcel
    @44
    @47
    @24
    wi
    #
    wi
    @32
    @32
    @33
    @43
    @49
    vz
    vw
    vv
    @13
    @13
    @16
    cvv
    cvv
    cvv
    vz
    vx
    weq
    #
    vw
    vx
    weq
    #
    vv
    vy
    weq
    #
    w3a
    #
    @41
    @47
    @42
    @24
    @53
    @37
    @45
    @40
    @46
    @53
    @36
    @25
    @5
    @50
    @51
    @36
    @25
    wceq
    @52
    @34
    @35
    @13
    @13
    opeq12
    3adant3
    eleq1d
    @53
    @39
    @26
    @5
    @50
    @52
    @39
    @26
    wceq
    @51
    @34
    @38
    @13
    @16
    opeq12
    3adant2
    eleq1d
    anbi12d
    @51
    @52
    @42
    @24
    wb
    @50
    @35
    @13
    @38
    @16
    eqeq12
    3adant1
    imbi12d
    spc3gv
    mp3an
    syl2im
    syl5bi
    @15
    @18
    @24
    @7
    wi
    @24
    @18
    @15
    @7
    @24
    @18
    @4
    @14
    wceq
    #
    @15
    @7
    wi
    @24
    @17
    @14
    @4
    @24
    @14
    @13
    @13
    cpr
    @17
    @13
    dfsn2
    @13
    @16
    @13
    preq2
    syl5req
    eqeq2d
    @15
    @54
    @7
    @3
    @4
    @14
    eqtr3
    expcom
    syl6bi
    com13
    imp
    sylcom
    exlimdvv
    mpd
    vtocl2g
    3impia
end
