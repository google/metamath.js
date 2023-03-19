include "c1stc.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wel.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpw.mm"
include "cuni.mm"
include "1stctop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cxp.mm"
include "cop.mm"
include "eqid.mm"
include "1stcclb.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "reeanv.mm"
include "an4.mm"
include "cmpt2.mm"
include "crn.mm"
include "wf.mm"
include "txopn.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "elpwi.mm"
include "ssralv.mm"
include "syl.mm"
include "ralimdv.mm"
include "sylan9.mm"
include "mpan9.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "ovex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "cen.mm"
include "vex.mm"
include "xpdom1.mm"
include "omex.mm"
include "xpdom2.mm"
include "domtr.mm"
include "xpomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "ondomen.mm"
include "sylancr.mm"
include "wfn.mm"
include "xpex.mm"
include "fnmpt2i.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fodomnum.mm"
include "mpisyl.mm"
include "syl2anc.mm"
include "ad2antrl.mm"
include "wb.mm"
include "anim12i.mm"
include "ad3antrrr.mm"
include "eltx.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "rspccv.mm"
include "r19.27v.mm"
include "r19.29.mm"
include "opelxp.mm"
include "pm3.35.mm"
include "an4s.mm"
include "sylanb.mm"
include "anim1i.mm"
include "anasss.mm"
include "an12s.mm"
include "expl.mm"
include "reximdv.mm"
include "syl5.mm"
include "impl.mm"
include "reximi.mm"
include "sylan.mm"
include "w3a.mm"
include "cab.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "eqidd.mm"
include "weq.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "elab.mm"
include "rnmpt2.mm"
include "syl6eleqr.mm"
include "simpr2.mm"
include "opelxpi.mm"
include "xpss12.mm"
include "simpr3.mm"
include "sstrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3exp2.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "impd.mm"
include "rexlimdvva.mm"
include "expd.mm"
include "impr.mm"
include "syl9r.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "breq1.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "ex.mm"
include "syl5bi.mm"
include "mp2and.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "ralxp.mm"
include "txuni.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "is1stc2.mm"
include "sylanbrc.mm"

theorem tx1stc
  let cR: class R
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R e. 1stc /\ S e. 1stc ) -> ( R tX S ) e. 1stc )

  proof
    cR
    c1stc
    wcel
    #
    cS
    c1stc
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
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
    @5
    wrex
    #
    wi
    #
    vz
    @3
    wral
    #
    wa
    #
    vy
    @3
    cpw
    #
    wrex
    #
    vx
    @3
    cuni
    #
    wral
    #
    @3
    c1stc
    wcel
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @4
    @1
    cR
    1stctop
    #
    cS
    1stctop
    #
    cR
    cS
    txtop
    syl2an
    @2
    @18
    vx
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    wral
    #
    @20
    @2
    @6
    vu
    cv
    #
    vv
    cv
    #
    cop
    #
    @10
    wcel
    #
    @31
    @9
    wcel
    #
    @11
    wa
    #
    vw
    @5
    wrex
    #
    wi
    #
    vz
    @3
    wral
    #
    wa
    #
    vy
    @17
    wrex
    #
    vv
    @26
    wral
    vu
    @25
    wral
    @28
    @2
    @39
    vu
    vv
    @25
    @26
    @2
    @29
    @25
    wcel
    #
    @30
    @26
    wcel
    #
    wa
    #
    wa
    #
    va
    cv
    #
    com
    cdom
    wbr
    #
    vu
    vr
    wel
    #
    vu
    vp
    wel
    #
    vp
    cv
    #
    vr
    cv
    #
    wss
    #
    wa
    #
    vp
    @44
    wrex
    #
    wi
    #
    vr
    cR
    wral
    #
    wa
    #
    va
    cR
    cpw
    #
    wrex
    #
    vb
    cv
    #
    com
    cdom
    wbr
    #
    vv
    vs
    wel
    #
    vv
    vq
    wel
    #
    vq
    cv
    #
    vs
    cv
    #
    wss
    #
    wa
    #
    vq
    @58
    wrex
    #
    wi
    #
    vs
    cS
    wral
    #
    wa
    #
    vb
    cS
    cpw
    #
    wrex
    #
    @39
    @0
    @40
    @57
    @1
    @41
    va
    vr
    vp
    @29
    cR
    @25
    @25
    eqid
    #
    1stcclb
    ad2ant2r
    @1
    @41
    @71
    @0
    @40
    vb
    vs
    vq
    @30
    cS
    @26
    @26
    eqid
    #
    1stcclb
    ad2ant2l
    @57
    @71
    wa
    @55
    @69
    wa
    #
    vb
    @70
    wrex
    va
    @56
    wrex
    @43
    @39
    @55
    @69
    va
    vb
    @56
    @70
    reeanv
    @43
    @74
    @39
    va
    vb
    @56
    @70
    @74
    @45
    @59
    wa
    #
    @54
    @68
    wa
    #
    wa
    #
    @43
    @44
    @56
    wcel
    #
    @58
    @70
    wcel
    #
    wa
    #
    wa
    #
    @39
    @45
    @54
    @59
    @68
    an4
    @81
    @77
    @39
    @81
    @77
    wa
    #
    vm
    vn
    @44
    @58
    vm
    cv
    #
    vn
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    @17
    wcel
    #
    @87
    com
    cdom
    wbr
    #
    @32
    @34
    vw
    @87
    wrex
    #
    wi
    #
    vz
    @3
    wral
    #
    @39
    @81
    @88
    @77
    @81
    @87
    @3
    wss
    #
    @88
    @81
    @44
    @58
    cxp
    #
    @3
    @86
    wf
    #
    @93
    @81
    @85
    @3
    wcel
    #
    vn
    @58
    wral
    #
    vm
    @44
    wral
    #
    @95
    @43
    @96
    vn
    cS
    wral
    #
    vm
    cR
    wral
    #
    @80
    @98
    @2
    @100
    @42
    @0
    @21
    @22
    @100
    @1
    @23
    @24
    @21
    @22
    wa
    #
    @96
    vm
    vn
    cR
    cS
    @83
    @84
    cR
    cS
    ctop
    ctop
    txopn
    ralrimivva
    syl2an
    adantr
    @78
    @100
    @99
    vm
    @44
    wral
    #
    @79
    @98
    @78
    @44
    cR
    wss
    @100
    @102
    wi
    @44
    cR
    elpwi
    @99
    vm
    @44
    cR
    ssralv
    syl
    @79
    @99
    @97
    vm
    @44
    @79
    @58
    cS
    wss
    @99
    @97
    wi
    @58
    cS
    elpwi
    @96
    vn
    @58
    cS
    ssralv
    syl
    ralimdv
    sylan9
    mpan9
    vm
    vn
    @44
    @58
    @85
    @3
    @86
    @86
    eqid
    #
    fmpt2
    sylib
    @94
    @3
    @86
    frn
    syl
    @87
    @3
    cR
    cS
    ctx
    ovex
    elpw2
    sylibr
    adantr
    @75
    @89
    @81
    @76
    @75
    @87
    @94
    cdom
    wbr
    #
    @94
    com
    cdom
    wbr
    #
    @89
    @75
    @94
    ccrd
    cdm
    wcel
    #
    @94
    @87
    @86
    wfo
    #
    @104
    @75
    com
    con0
    wcel
    @105
    @106
    omelon
    @75
    @94
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @108
    com
    cen
    wbr
    @105
    @45
    @94
    com
    @58
    cxp
    #
    cdom
    wbr
    @110
    @108
    cdom
    wbr
    @109
    @59
    @44
    com
    @58
    vb
    vex
    xpdom1
    @58
    com
    com
    omex
    xpdom2
    @94
    @110
    @108
    domtr
    syl2an
    xpomen
    @94
    @108
    com
    domentr
    sylancl
    #
    com
    @94
    ondomen
    sylancr
    @86
    @94
    wfn
    @107
    vm
    vn
    @44
    @58
    @85
    @86
    @103
    @83
    @84
    vm
    vex
    vn
    vex
    xpex
    fnmpt2i
    @94
    @86
    dffn4
    mpbi
    @94
    @87
    @86
    fodomnum
    mpisyl
    @111
    @87
    @94
    com
    domtr
    syl2anc
    ad2antrl
    @82
    @91
    vz
    @3
    @82
    @10
    @3
    wcel
    #
    @9
    @49
    @63
    cxp
    #
    wcel
    #
    @113
    @10
    wss
    #
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    #
    vw
    @10
    wral
    #
    @91
    @82
    @101
    @112
    @118
    wb
    @2
    @101
    @42
    @80
    @77
    @0
    @21
    @1
    @22
    @23
    @24
    anim12i
    ad3antrrr
    vr
    vs
    @10
    cR
    cS
    ctop
    ctop
    vw
    eltx
    syl
    @118
    @32
    @31
    @113
    wcel
    #
    @115
    wa
    #
    vs
    cS
    wrex
    #
    vr
    cR
    wrex
    #
    @82
    @90
    @117
    @122
    vw
    @31
    @10
    @9
    @31
    wceq
    #
    @116
    @120
    vr
    vs
    cR
    cS
    @123
    @114
    @119
    @115
    @9
    @31
    @113
    eleq1
    anbi1d
    2rexbidv
    rspccv
    @81
    @75
    @76
    @122
    @90
    wi
    @81
    @75
    wa
    #
    @76
    @122
    @90
    @76
    @122
    wa
    @52
    @66
    wa
    #
    @115
    wa
    #
    vs
    cS
    wrex
    #
    vr
    cR
    wrex
    #
    @124
    @90
    @76
    @53
    @68
    wa
    #
    vr
    cR
    wral
    #
    @122
    @128
    @53
    @68
    vr
    cR
    r19.27v
    @130
    @122
    wa
    @129
    @121
    wa
    #
    vr
    cR
    wrex
    @128
    @129
    @121
    vr
    cR
    r19.29
    @131
    @127
    vr
    cR
    @53
    @68
    @121
    @127
    @68
    @121
    wa
    @67
    @120
    wa
    #
    vs
    cS
    wrex
    @53
    @127
    @67
    @120
    vs
    cS
    r19.29
    @53
    @132
    @126
    vs
    cS
    @53
    @67
    @120
    @126
    @119
    @53
    @67
    wa
    #
    @115
    @126
    @119
    @133
    @115
    @126
    @119
    @133
    wa
    @125
    @115
    @119
    @46
    @60
    wa
    @133
    @125
    @29
    @30
    @49
    @63
    opelxp
    @46
    @53
    @60
    @67
    @125
    @46
    @53
    wa
    @52
    @60
    @67
    wa
    @66
    @46
    @52
    pm3.35
    @60
    @66
    pm3.35
    anim12i
    an4s
    sylanb
    anim1i
    anasss
    an12s
    expl
    reximdv
    syl5
    impl
    reximi
    syl
    sylan
    @124
    @126
    @90
    vr
    vs
    cR
    cS
    @124
    @49
    cR
    wcel
    @63
    cS
    wcel
    wa
    wa
    #
    @125
    @115
    @90
    @125
    @51
    @65
    wa
    #
    vq
    @58
    wrex
    vp
    @44
    wrex
    @134
    @115
    @90
    wi
    #
    @51
    @65
    vp
    vq
    @44
    @58
    reeanv
    @134
    @135
    @136
    vp
    vq
    @44
    @58
    @134
    vp
    va
    wel
    #
    vq
    vb
    wel
    #
    wa
    #
    @135
    @115
    @90
    @134
    @139
    @135
    @115
    w3a
    wa
    #
    @48
    @62
    cxp
    #
    @87
    wcel
    @31
    @141
    wcel
    #
    @141
    @10
    wss
    #
    @90
    @140
    @141
    vx
    cv
    #
    @85
    wceq
    #
    vn
    @58
    wrex
    vm
    @44
    wrex
    #
    vx
    cab
    #
    @87
    @140
    @141
    @85
    wceq
    #
    vn
    @58
    wrex
    vm
    @44
    wrex
    #
    @141
    @147
    wcel
    @140
    @137
    @138
    @141
    @141
    wceq
    #
    @149
    @137
    @138
    @135
    @115
    @134
    simpr1l
    @137
    @138
    @135
    @115
    @134
    simpr1r
    @140
    @141
    eqidd
    @148
    @150
    @141
    @48
    @84
    cxp
    #
    wceq
    vm
    vn
    @48
    @62
    @44
    @58
    vm
    vp
    weq
    @85
    @151
    @141
    @83
    @48
    @84
    xpeq1
    eqeq2d
    vn
    vq
    weq
    @151
    @141
    @141
    @84
    @62
    @48
    xpeq2
    eqeq2d
    rspc2ev
    syl3anc
    @146
    @149
    vx
    @141
    @48
    @62
    vp
    vex
    vq
    vex
    xpex
    @144
    @141
    wceq
    @145
    @148
    vm
    vn
    @44
    @58
    @144
    @141
    @85
    eqeq1
    2rexbidv
    elab
    sylibr
    vm
    vn
    vx
    @44
    @58
    @85
    @86
    @103
    rnmpt2
    syl6eleqr
    @140
    @135
    @142
    @134
    @139
    @135
    @115
    simpr2
    #
    @47
    @61
    @142
    @50
    @64
    @29
    @30
    @48
    @62
    opelxpi
    ad2ant2r
    syl
    @140
    @141
    @113
    @10
    @140
    @135
    @141
    @113
    wss
    #
    @152
    @50
    @64
    @153
    @47
    @61
    @48
    @49
    @62
    @63
    xpss12
    ad2ant2l
    syl
    @134
    @139
    @135
    @115
    simpr3
    sstrd
    @34
    @142
    @143
    wa
    vw
    @141
    @87
    @9
    @141
    wceq
    @33
    @142
    @11
    @143
    @9
    @141
    @31
    eleq2
    @9
    @141
    @10
    sseq1
    anbi12d
    rspcev
    syl12anc
    3exp2
    rexlimdvv
    syl5bir
    impd
    rexlimdvva
    syl5
    expd
    impr
    syl9r
    sylbid
    ralrimiv
    @38
    @89
    @92
    wa
    vy
    @87
    @17
    @5
    @87
    wceq
    #
    @6
    @89
    @37
    @92
    @5
    @87
    com
    cdom
    breq1
    @154
    @36
    @91
    vz
    @3
    @154
    @35
    @90
    @32
    @34
    vw
    @5
    @87
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    ex
    syl5bi
    rexlimdvva
    syl5bir
    mp2and
    ralrimivva
    @18
    @39
    vx
    vu
    vv
    @25
    @26
    @144
    @31
    wceq
    #
    @16
    @38
    vy
    @17
    @155
    @15
    @37
    @6
    @155
    @14
    @36
    vz
    @3
    @155
    @7
    @32
    @13
    @35
    @144
    @31
    @10
    eleq1
    @155
    @12
    @34
    vw
    @5
    @155
    @8
    @33
    @11
    @144
    @31
    @9
    eleq1
    anbi1d
    rexbidv
    imbi12d
    ralbidv
    anbi2d
    rexbidv
    ralxp
    sylibr
    @2
    @18
    vx
    @27
    @19
    @0
    @21
    @22
    @27
    @19
    wceq
    @1
    @23
    @24
    cR
    cS
    @25
    @26
    @72
    @73
    txuni
    syl2an
    raleqdv
    mpbid
    vx
    vy
    vz
    vw
    @3
    @19
    @19
    eqid
    is1stc2
    sylanbrc
end
