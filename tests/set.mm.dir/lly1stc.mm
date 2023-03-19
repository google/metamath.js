include "c1stc.mm"
include "clly.mm"
include "cv.mm"
include "wcel.mm"
include "ctop.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wel.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpw.mm"
include "cuni.mm"
include "llytop.mm"
include "crest.mm"
include "co.mm"
include "w3a.mm"
include "simprr.mm"
include "simprl.mm"
include "wceq.mm"
include "ad3antrrr.mm"
include "elssuni.mm"
include "ad2antlr.mm"
include "eqid.mm"
include "restuni.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "1stcclb.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "elpwi.mm"
include "adantl.mm"
include "sselda.mm"
include "wb.mm"
include "adantr.mm"
include "simpllr.mm"
include "restopn2.mm"
include "simplbda.mm"
include "syldan.mm"
include "df-ss.mm"
include "sylib.mm"
include "simprbda.mm"
include "eqeltrd.mm"
include "ineq1.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "adantrr.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "simprrl.mm"
include "1stcrestlem.mm"
include "ad2antrr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "simprrr.mm"
include "elind.mm"
include "eleq2.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "elin.mm"
include "simplbi2com.mm"
include "biantrud.mm"
include "ssin.mm"
include "syl6bb.mm"
include "ssinss1.mm"
include "syl6bir.mm"
include "anim12d.mm"
include "reximdva.mm"
include "cvv.mm"
include "inex1.mm"
include "rgenw.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "syl6ibr.mm"
include "mpd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "3adantr1.mm"
include "simpl.mm"
include "topopn.mm"
include "simpr.mm"
include "llyi.mm"
include "r19.29a.mm"
include "is1stc2.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "wtru.mm"
include "1stcrest.mm"
include "1stctop.mm"
include "a1i.mm"
include "restlly.mm"
include "trud.mm"
include "eqssi.mm"

theorem lly1stc
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cA: class A
  let cV: class V
  let cX: class X
  let cJ: class J


  assert |- Locally 1stc = 1stc

  proof
    c1stc
    clly
    #
    c1stc
    vj
    @0
    c1stc
    vj
    cv
    #
    @0
    wcel
    #
    @1
    ctop
    wcel
    #
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    vz
    wel
    #
    vx
    vw
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
    wa
    #
    vw
    @4
    wrex
    #
    wi
    #
    vz
    @1
    wral
    #
    wa
    #
    vy
    @1
    cpw
    #
    wrex
    #
    vx
    @1
    cuni
    #
    wral
    @1
    c1stc
    wcel
    #
    c1stc
    @1
    llytop
    #
    @2
    @17
    vx
    @18
    @2
    vx
    cv
    #
    @18
    wcel
    #
    wa
    #
    vu
    cv
    #
    @18
    wss
    #
    vx
    vu
    wel
    #
    @1
    @24
    crest
    co
    #
    c1stc
    wcel
    #
    w3a
    #
    @17
    vu
    @1
    @23
    vu
    vj
    wel
    #
    wa
    #
    @26
    @28
    @17
    @25
    @31
    @26
    @28
    wa
    #
    wa
    #
    vt
    cv
    #
    com
    cdom
    wbr
    #
    vx
    vv
    wel
    #
    vx
    vn
    wel
    #
    vn
    cv
    #
    vv
    cv
    #
    wss
    #
    wa
    #
    vn
    @34
    wrex
    #
    wi
    #
    vv
    @27
    wral
    #
    wa
    #
    @17
    vt
    @27
    cpw
    #
    @33
    @28
    @21
    @27
    cuni
    #
    wcel
    @45
    vt
    @46
    wrex
    @31
    @26
    @28
    simprr
    @33
    @21
    @24
    @47
    @31
    @26
    @28
    simprl
    #
    @33
    @3
    @25
    @24
    @47
    wceq
    @2
    @3
    @22
    @30
    @32
    @20
    ad3antrrr
    #
    @30
    @25
    @23
    @32
    @24
    @1
    elssuni
    ad2antlr
    @24
    @1
    @18
    @18
    eqid
    #
    restuni
    syl2anc
    eleqtrd
    vt
    vv
    vn
    @21
    @27
    @47
    @47
    eqid
    1stcclb
    syl2anc
    @33
    @34
    @46
    wcel
    #
    @45
    wa
    #
    wa
    #
    va
    @34
    va
    cv
    #
    @24
    cin
    #
    cmpt
    #
    crn
    #
    @16
    wcel
    #
    @57
    com
    cdom
    wbr
    #
    @6
    @11
    vw
    @57
    wrex
    #
    wi
    #
    vz
    @1
    wral
    #
    @17
    @53
    @57
    @1
    wss
    #
    @58
    @33
    @51
    @63
    @45
    @33
    @51
    wa
    #
    @34
    @1
    @56
    wf
    @63
    @64
    vn
    @34
    @38
    @24
    cin
    #
    @1
    @56
    @64
    vn
    vt
    wel
    #
    wa
    #
    @65
    @38
    @1
    @67
    @38
    @24
    wss
    #
    @65
    @38
    wceq
    @64
    @66
    @38
    @27
    wcel
    #
    @68
    @64
    @34
    @27
    @38
    @51
    @34
    @27
    wss
    @33
    @34
    @27
    elpwi
    adantl
    sselda
    #
    @64
    @69
    vn
    vj
    wel
    #
    @68
    @64
    @3
    @30
    @69
    @71
    @68
    wa
    wb
    @33
    @3
    @51
    @49
    adantr
    @23
    @30
    @32
    @51
    simpllr
    @24
    @38
    @1
    restopn2
    syl2anc
    #
    simplbda
    syldan
    #
    @38
    @24
    df-ss
    sylib
    @64
    @66
    @69
    @71
    @70
    @64
    @69
    @71
    @68
    @72
    simprbda
    syldan
    eqeltrd
    va
    vn
    @34
    @55
    @65
    @54
    @38
    @24
    ineq1
    cbvmptv
    #
    fmptd
    @34
    @1
    @56
    frn
    syl
    adantrr
    @57
    @1
    vj
    vex
    elpw2
    sylibr
    @53
    @35
    @59
    @33
    @51
    @35
    @44
    simprrl
    va
    @34
    @55
    1stcrestlem
    syl
    @53
    @61
    vz
    @1
    @53
    vz
    vj
    wel
    #
    @6
    @60
    @53
    @75
    @6
    wa
    #
    wa
    #
    @37
    @38
    @9
    @24
    cin
    #
    wss
    #
    wa
    #
    vn
    @34
    wrex
    #
    @60
    @77
    @78
    @27
    wcel
    #
    @44
    @21
    @78
    wcel
    #
    @81
    @77
    @3
    @30
    @75
    @82
    @33
    @3
    @52
    @76
    @49
    ad2antrr
    @53
    @30
    @76
    @23
    @30
    @32
    @52
    simpllr
    adantr
    @53
    @75
    @6
    simprl
    @9
    @24
    @1
    ctop
    @1
    elrestr
    syl3anc
    @53
    @44
    @76
    @33
    @51
    @35
    @44
    simprrr
    adantr
    @77
    @9
    @24
    @21
    @53
    @75
    @6
    simprr
    @33
    @26
    @52
    @76
    @48
    ad2antrr
    elind
    @43
    @83
    @81
    wi
    vv
    @78
    @27
    @39
    @78
    wceq
    #
    @36
    @83
    @42
    @81
    @39
    @78
    @21
    eleq2
    @84
    @41
    @80
    vn
    @34
    @84
    @40
    @79
    @37
    @39
    @78
    @38
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl3c
    @53
    @81
    @60
    wi
    #
    @76
    @33
    @51
    @85
    @45
    @64
    @81
    @21
    @65
    wcel
    #
    @65
    @9
    wss
    #
    wa
    #
    vn
    @34
    wrex
    #
    @60
    @64
    @80
    @88
    vn
    @34
    @67
    @37
    @86
    @79
    @87
    @67
    @26
    @37
    @86
    wi
    @33
    @26
    @51
    @66
    @48
    ad2antrr
    @86
    @37
    @26
    @21
    @38
    @24
    elin
    simplbi2com
    syl
    @67
    @79
    @38
    @9
    wss
    #
    @87
    @67
    @90
    @90
    @68
    wa
    @79
    @67
    @68
    @90
    @73
    biantrud
    @38
    @9
    @24
    ssin
    syl6bb
    @38
    @24
    @9
    ssinss1
    syl6bir
    anim12d
    reximdva
    @65
    cvv
    wcel
    #
    vn
    @34
    wral
    @60
    @89
    wb
    @91
    vn
    @34
    @38
    @24
    vn
    vex
    inex1
    rgenw
    @11
    @88
    vn
    vw
    @34
    @65
    @56
    cvv
    @74
    @8
    @65
    wceq
    @7
    @86
    @10
    @87
    @8
    @65
    @21
    eleq2
    @8
    @65
    @9
    sseq1
    anbi12d
    rexrnmpt
    ax-mp
    syl6ibr
    adantrr
    adantr
    mpd
    expr
    ralrimiva
    @15
    @59
    @62
    wa
    vy
    @57
    @16
    @4
    @57
    wceq
    #
    @5
    @59
    @14
    @62
    @4
    @57
    com
    cdom
    breq1
    @92
    @13
    @61
    vz
    @1
    @92
    @12
    @60
    @6
    @11
    vw
    @4
    @57
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    3adantr1
    @23
    @2
    @18
    @1
    wcel
    #
    @22
    @29
    vu
    @1
    wrex
    @2
    @22
    simpl
    @23
    @3
    @93
    @2
    @3
    @22
    @20
    adantr
    @1
    @18
    @50
    topopn
    syl
    @2
    @22
    simpr
    vu
    c1stc
    @21
    @18
    @1
    llyi
    syl3anc
    r19.29a
    ralrimiva
    vx
    vy
    vz
    vw
    @1
    @18
    @50
    is1stc2
    sylanbrc
    ssriv
    c1stc
    @0
    wss
    wtru
    vx
    c1stc
    vj
    @19
    vx
    vj
    wel
    wa
    @1
    @21
    crest
    co
    c1stc
    wcel
    wtru
    @21
    @1
    @1
    1stcrest
    adantl
    c1stc
    ctop
    wss
    wtru
    vj
    c1stc
    ctop
    @1
    1stctop
    ssriv
    a1i
    restlly
    trud
    eqssi
end
