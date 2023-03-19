include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "c1st.mm"
include "cvv.mm"
include "cid.mm"
include "cdif.mm"
include "c2nd.mm"
include "ccom.mm"
include "ctxp.mm"
include "wbr.mm"
include "wex.mm"
include "wn.mm"
include "wfun.mm"
include "cfuns.mm"
include "wceq.mm"
include "elrel.mm"
include "ex.mm"
include "anim12d.mm"
include "adantrd.mm"
include "pm4.71rd.mm"
include "19.41vvvv.mm"
include "ee4anv.mm"
include "anbi1i.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "2exbidv.mm"
include "excom13.mm"
include "exrot4.mm"
include "excom.mm"
include "w3a.mm"
include "df-3an.mm"
include "2exbii.mm"
include "opex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "breq1.mm"
include "vex.mm"
include "brtxp.mm"
include "br1steq.mm"
include "equcom.mm"
include "bitri.mm"
include "brco.mm"
include "br2ndeq.mm"
include "exbii.mm"
include "brv.mm"
include "brdif.mm"
include "mpbiran.mm"
include "ideq.mm"
include "notbii.mm"
include "equsexvw.mm"
include "3bitri.mm"
include "anbi12i.mm"
include "an12.mm"
include "ceqsex2v.mm"
include "bitr3i.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "exanali.mm"
include "exnal.mm"
include "con2bid.mm"
include "pm5.32i.mm"
include "dffun4.mm"
include "cxp.mm"
include "cpw.mm"
include "cep.mm"
include "ccnv.mm"
include "cfix.mm"
include "df-funs.mm"
include "eleq2i.mm"
include "eldif.mm"
include "wss.mm"
include "elpw.mm"
include "df-rel.mm"
include "bitr4i.mm"
include "wrex.mm"
include "elfix.mm"
include "coep.mm"
include "coepr.mm"
include "rexbii.mm"
include "r2ex.mm"
include "3bitr4ri.mm"

theorem elfuns
  let cF: class F
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  assume elfuns.1: |- F e. _V


  assert |- ( F e. Funs <-> Fun F )

  proof
    cF
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    @1
    vz
    cv
    #
    cop
    #
    cF
    wcel
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    wa
    @0
    vp
    cv
    #
    cF
    wcel
    #
    vq
    cv
    #
    cF
    wcel
    #
    wa
    #
    @15
    @13
    c1st
    cvv
    cid
    cdif
    #
    c2nd
    ccom
    #
    ctxp
    #
    wbr
    #
    wa
    #
    vq
    wex
    vp
    wex
    #
    wn
    #
    wa
    #
    cF
    wfun
    cF
    cfuns
    wcel
    #
    @0
    @12
    @24
    @0
    @23
    @12
    @0
    @23
    @13
    @3
    wceq
    #
    @15
    va
    cv
    #
    @5
    cop
    #
    wceq
    #
    wa
    #
    @22
    wa
    #
    vz
    wex
    va
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    vq
    wex
    vp
    wex
    #
    @12
    wn
    #
    @0
    @22
    @35
    vp
    vq
    @0
    @22
    @27
    vy
    wex
    vx
    wex
    #
    @30
    vz
    wex
    va
    wex
    #
    wa
    #
    @22
    wa
    #
    @35
    @0
    @22
    @40
    @0
    @17
    @40
    @21
    @0
    @14
    @38
    @16
    @39
    @0
    @14
    @38
    vx
    vy
    @13
    cF
    elrel
    ex
    @0
    @16
    @39
    va
    vz
    @15
    cF
    elrel
    ex
    anim12d
    adantrd
    pm4.71rd
    @35
    @31
    vz
    wex
    va
    wex
    vy
    wex
    vx
    wex
    #
    @22
    wa
    @41
    @31
    @22
    vy
    va
    vz
    vx
    19.41vvvv
    @42
    @40
    @22
    @27
    @30
    vx
    vy
    va
    vz
    ee4anv
    anbi1i
    bitr2i
    syl6bb
    2exbidv
    @36
    @34
    vp
    wex
    vq
    wex
    #
    vx
    wex
    @11
    wn
    #
    vx
    wex
    @37
    @34
    vp
    vq
    vx
    excom13
    @43
    @44
    vx
    @43
    @33
    vq
    wex
    vp
    wex
    #
    vy
    wex
    @10
    wn
    #
    vy
    wex
    @44
    @33
    vq
    vp
    vy
    excom13
    @45
    @46
    vy
    @45
    @32
    vq
    wex
    vp
    wex
    #
    vz
    wex
    va
    wex
    @47
    va
    wex
    #
    vz
    wex
    #
    @46
    @32
    vp
    vq
    va
    vz
    exrot4
    @47
    va
    vz
    excom
    @49
    @8
    @9
    wn
    #
    wa
    #
    vz
    wex
    @46
    @48
    @51
    vz
    @48
    va
    vx
    weq
    #
    @4
    @29
    cF
    wcel
    #
    wa
    #
    @50
    wa
    #
    wa
    #
    va
    wex
    @51
    @47
    @56
    va
    @47
    @27
    @30
    @22
    w3a
    #
    vq
    wex
    vp
    wex
    @56
    @57
    @32
    vp
    vq
    @27
    @30
    @22
    df-3an
    2exbii
    @22
    @4
    @16
    wa
    #
    @15
    @3
    @20
    wbr
    #
    wa
    #
    @56
    vp
    vq
    @3
    @29
    @1
    @2
    opex
    @28
    @5
    opex
    #
    @27
    @17
    @58
    @21
    @59
    @27
    @14
    @4
    @16
    @13
    @3
    cF
    eleq1
    anbi1d
    @13
    @3
    @15
    @20
    breq2
    anbi12d
    @30
    @60
    @54
    @52
    @50
    wa
    #
    wa
    @56
    @30
    @58
    @54
    @59
    @62
    @30
    @16
    @53
    @4
    @15
    @29
    cF
    eleq1
    anbi2d
    @30
    @59
    @29
    @3
    @20
    wbr
    #
    @62
    @15
    @29
    @3
    @20
    breq1
    @63
    @29
    @1
    c1st
    wbr
    #
    @29
    @2
    @19
    wbr
    #
    wa
    @62
    c1st
    @19
    @29
    @1
    @2
    @61
    vx
    vex
    vy
    vex
    #
    brtxp
    @64
    @52
    @65
    @50
    @64
    vx
    va
    weq
    @52
    @28
    @5
    @1
    va
    vex
    #
    vz
    vex
    #
    br1steq
    vx
    va
    equcom
    bitri
    @65
    @29
    @1
    c2nd
    wbr
    #
    @1
    @2
    @18
    wbr
    #
    wa
    #
    vx
    wex
    vx
    vz
    weq
    #
    @70
    wa
    #
    vx
    wex
    @50
    vx
    @29
    @2
    @18
    c2nd
    @61
    @66
    brco
    @71
    @73
    vx
    @69
    @72
    @70
    @28
    @5
    @1
    @67
    @68
    br2ndeq
    anbi1i
    exbii
    @70
    @50
    vx
    vz
    @72
    @70
    @5
    @2
    @18
    wbr
    #
    @50
    @1
    @5
    @2
    @18
    breq1
    @74
    @5
    @2
    cid
    wbr
    #
    wn
    #
    @50
    @74
    @5
    @2
    cvv
    wbr
    @76
    @5
    @2
    brv
    @5
    @2
    cvv
    cid
    brdif
    mpbiran
    @75
    @9
    @75
    vz
    vy
    weq
    @9
    @5
    @2
    @66
    ideq
    vz
    vy
    equcom
    bitri
    notbii
    bitri
    syl6bb
    equsexvw
    3bitri
    anbi12i
    bitri
    syl6bb
    anbi12d
    @54
    @52
    @50
    an12
    syl6bb
    ceqsex2v
    bitr3i
    exbii
    @55
    @51
    va
    vx
    @52
    @54
    @8
    @50
    @52
    @53
    @7
    @4
    @52
    @29
    @6
    cF
    @28
    @1
    @5
    opeq1
    eleq1d
    anbi2d
    anbi1d
    equsexvw
    bitri
    exbii
    @8
    @9
    vz
    exanali
    bitri
    3bitri
    exbii
    @10
    vy
    exnal
    3bitri
    exbii
    @11
    vx
    exnal
    3bitri
    syl6bb
    con2bid
    pm5.32i
    vx
    vy
    vz
    cF
    dffun4
    @26
    cF
    cvv
    cvv
    cxp
    #
    cpw
    #
    cep
    @20
    cep
    ccnv
    ccom
    #
    ccom
    #
    cfix
    #
    cdif
    #
    wcel
    cF
    @78
    wcel
    #
    cF
    @81
    wcel
    #
    wn
    #
    wa
    @25
    cfuns
    @82
    cF
    df-funs
    eleq2i
    cF
    @78
    @81
    eldif
    @83
    @0
    @85
    @24
    @83
    cF
    @77
    wss
    @0
    cF
    @77
    elfuns.1
    elpw
    cF
    df-rel
    bitr4i
    @84
    @23
    @84
    cF
    cF
    @80
    wbr
    #
    @21
    vq
    cF
    wrex
    #
    vp
    cF
    wrex
    #
    @23
    cF
    @80
    elfuns.1
    elfix
    @86
    cF
    @13
    @79
    wbr
    #
    vp
    cF
    wrex
    @88
    vp
    cF
    cF
    @79
    elfuns.1
    elfuns.1
    coep
    @89
    @87
    vp
    cF
    vq
    cF
    @13
    @20
    elfuns.1
    vp
    vex
    coepr
    rexbii
    bitri
    @21
    vp
    vq
    cF
    cF
    r2ex
    3bitri
    notbii
    anbi12i
    3bitri
    3bitr4ri
end
