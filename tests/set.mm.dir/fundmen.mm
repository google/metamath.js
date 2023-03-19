include "wfun.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "dmex.mm"
include "a1i.mm"
include "funfvop.mm"
include "ex.mm"
include "wrel.mm"
include "wi.mm"
include "funrel.mm"
include "elreldm.mm"
include "syl.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "wex.mm"
include "cxp.mm"
include "wss.mm"
include "df-rel.mm"
include "sylib.mm"
include "sselda.mm"
include "elvv.mm"
include "inteq.mm"
include "inteqd.mm"
include "vex.mm"
include "op1stb.mm"
include "syl6eq.mm"
include "eqeq1.mm"
include "syl5ibr.mm"
include "opeq1.mm"
include "syl6.mm"
include "imp.mm"
include "eqeq2.mm"
include "biimprcd.mm"
include "adantl.mm"
include "mpd.mm"
include "ancoms.mm"
include "eleq1d.mm"
include "funopfv.mm"
include "adantr.mm"
include "sylbid.mm"
include "exp32.mm"
include "com24.mm"
include "imp43.mm"
include "opeq2d.mm"
include "eqtr4d.mm"
include "exlimdvv.mm"
include "adantrl.mm"
include "fvex.mm"
include "syl6req.mm"
include "impbid1.mm"
include "en3d.mm"

theorem fundmen
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume fundmen.1: |- F e. _V


  assert |- ( Fun F -> dom F ~~ F )

  proof
    cF
    wfun
    #
    vx
    vy
    cF
    cdm
    #
    cF
    vx
    cv
    #
    @2
    cF
    cfv
    #
    cop
    #
    vy
    cv
    #
    cint
    #
    cint
    #
    @1
    cvv
    wcel
    @0
    cF
    fundmen.1
    dmex
    a1i
    cF
    cvv
    wcel
    @0
    fundmen.1
    a1i
    @0
    @2
    @1
    wcel
    #
    @4
    cF
    wcel
    @2
    cF
    funfvop
    ex
    @0
    cF
    wrel
    #
    @5
    cF
    wcel
    #
    @7
    @1
    wcel
    #
    wi
    cF
    funrel
    #
    @9
    @10
    @11
    cF
    @5
    elreldm
    ex
    syl
    @0
    @8
    @10
    wa
    #
    @2
    @7
    wceq
    #
    @5
    @4
    wceq
    #
    wb
    @0
    @13
    wa
    @14
    @15
    @0
    @10
    @14
    @15
    wi
    #
    @8
    @0
    @10
    wa
    #
    @5
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    vw
    wex
    vz
    wex
    #
    @16
    @17
    @5
    cvv
    cvv
    cxp
    #
    wcel
    @22
    @0
    cF
    @23
    @5
    @0
    @9
    cF
    @23
    wss
    @12
    cF
    df-rel
    sylib
    sselda
    vz
    vw
    @5
    elvv
    sylib
    @17
    @21
    @16
    vz
    vw
    @17
    @21
    @14
    @15
    @17
    @21
    @14
    wa
    #
    wa
    #
    @5
    @2
    @19
    cop
    #
    @4
    @24
    @5
    @26
    wceq
    #
    @17
    @14
    @21
    @27
    @14
    @21
    wa
    #
    @26
    @20
    wceq
    #
    @27
    @14
    @21
    @29
    @14
    @21
    @2
    @18
    wceq
    #
    @29
    @21
    @30
    @14
    @7
    @18
    wceq
    @21
    @7
    @20
    cint
    #
    cint
    @18
    @21
    @6
    @31
    @5
    @20
    inteq
    inteqd
    @18
    @19
    vz
    vex
    vw
    vex
    op1stb
    syl6eq
    @2
    @7
    @18
    eqeq1
    syl5ibr
    @2
    @18
    @19
    opeq1
    syl6
    imp
    @21
    @29
    @27
    wi
    @14
    @29
    @27
    @21
    @26
    @20
    @5
    eqeq2
    biimprcd
    adantl
    mpd
    #
    ancoms
    adantl
    @25
    @3
    @19
    @2
    @0
    @10
    @21
    @14
    @3
    @19
    wceq
    #
    @0
    @14
    @21
    @10
    @33
    @0
    @14
    @21
    @10
    @33
    wi
    @0
    @28
    wa
    @10
    @26
    cF
    wcel
    #
    @33
    @28
    @10
    @34
    wb
    @0
    @28
    @5
    @26
    cF
    @32
    eleq1d
    adantl
    @0
    @34
    @33
    wi
    @28
    @2
    @19
    cF
    funopfv
    adantr
    sylbid
    exp32
    com24
    imp43
    opeq2d
    eqtr4d
    exp32
    exlimdvv
    mpd
    adantrl
    @15
    @7
    @4
    cint
    #
    cint
    @2
    @15
    @6
    @35
    @5
    @4
    inteq
    inteqd
    @2
    @3
    vx
    vex
    @2
    cF
    fvex
    op1stb
    syl6req
    impbid1
    ex
    en3d
end
