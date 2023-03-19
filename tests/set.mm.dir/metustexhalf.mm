include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "wceq.mm"
include "ccom.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "simp-4r.mm"
include "simplr.mm"
include "rphalfcld.mm"
include "eqidd.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "crn.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "eqtri.mm"
include "metustel.mm"
include "biimpar.mm"
include "wrel.mm"
include "relco.mm"
include "a1i.mm"
include "cop.mm"
include "cxp.mm"
include "cdm.mm"
include "cossxp.mm"
include "cnvimass.mm"
include "cxr.mm"
include "wf.mm"
include "psmetf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "dmss.mm"
include "rnss.mm"
include "xpss12.mm"
include "adantl.mm"
include "dmxp.mm"
include "rnxp.mm"
include "xpeq12d.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "syl5ss.mm"
include "ad3antrrr.mm"
include "sselda.mm"
include "opelxp.mm"
include "sylib.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "w3a.mm"
include "wbr.mm"
include "simplll.mm"
include "simp1d.mm"
include "jca.mm"
include "simp2d.mm"
include "simp3d.mm"
include "3jca.mm"
include "wfun.mm"
include "simpld.mm"
include "ffun.mm"
include "sylanbrc.mm"
include "eleqtrrd.mm"
include "cle.mm"
include "clt.mm"
include "0xr.mm"
include "simprd.mm"
include "rpxrd.mm"
include "ffvelrnd.mm"
include "psmetge0.mm"
include "syl3anc.mm"
include "df-ov.mm"
include "syl6breq.mm"
include "cxad.mm"
include "syl5eqel.mm"
include "caddc.mm"
include "cr.mm"
include "0red.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "rexrd.mm"
include "df-br.mm"
include "fvimacnv.mm"
include "syl21anc.mm"
include "elico2.mm"
include "biimpa.mm"
include "rexadd.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "psmettri.mm"
include "syl13anc.mm"
include "lt2halvesd.mm"
include "eqbrtrd.mm"
include "xrlelttrd.mm"
include "syl5eqbrr.mm"
include "elico1.mm"
include "syl23anc.mm"
include "sylibr.mm"
include "syl22anc.mm"
include "breqd.mm"
include "mpbird.mm"
include "wex.mm"
include "simpr.mm"
include "vex.mm"
include "brco.mm"
include "wi.mm"
include "brelrn.mm"
include "sseldd.mm"
include "adantrr.mm"
include "ex.mm"
include "ancrd.mm"
include "eximdv.mm"
include "3ad2ant1.mm"
include "mpd.mm"
include "df-rex.mm"
include "r19.29a.mm"
include "syl31anc.mm"
include "mpdan.mm"
include "relssdv.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq1d.mm"
include "wb.mm"

theorem metustexhalf
  let vv: setvar v
  let cA: class A
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint A a
  disjoint F a
  disjoint a v
  disjoint A v
  disjoint D v
  disjoint F v
  disjoint X v
  disjoint B a
  disjoint a b
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  disjoint a p
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint a x
  disjoint p x
  disjoint D p
  disjoint q x
  disjoint D q
  disjoint D x
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X p
  disjoint X q
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a r
  disjoint p r
  disjoint p v
  disjoint q r
  disjoint q v
  disjoint r v
  disjoint A r
  disjoint a u
  disjoint a w
  disjoint r u
  disjoint r w
  disjoint D r
  disjoint u v
  disjoint u w
  disjoint D u
  disjoint v w
  disjoint D w
  disjoint F r
  disjoint F u
  disjoint F w
  disjoint X r
  disjoint X u
  disjoint X w
  assert |- ( ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) /\ A e. F ) -> E. v e. F ( v o. v ) C_ A )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    wa
    #
    cA
    cF
    wcel
    #
    wa
    #
    cA
    cD
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    vv
    cv
    #
    @10
    ccom
    #
    cA
    wss
    #
    vv
    cF
    wrex
    #
    va
    crp
    @4
    @6
    crp
    wcel
    #
    wa
    #
    @9
    wa
    #
    @5
    cc0
    @6
    c2
    cdiv
    co
    #
    cico
    co
    #
    cima
    #
    cF
    wcel
    #
    @19
    @19
    ccom
    #
    cA
    wss
    #
    @13
    @16
    @1
    @19
    @5
    cc0
    vb
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    vb
    crp
    wrex
    #
    @20
    @0
    @1
    @3
    @14
    @9
    simp-4r
    #
    @16
    @17
    crp
    wcel
    @19
    @19
    wceq
    #
    @27
    @16
    @6
    @4
    @14
    @9
    simplr
    #
    rphalfcld
    @16
    @19
    eqidd
    @26
    @29
    vb
    @17
    crp
    @23
    @17
    wceq
    #
    @25
    @19
    @19
    @31
    @24
    @18
    @5
    @23
    @17
    cc0
    cico
    oveq2
    imaeq2d
    eqeq2d
    rspcev
    syl2anc
    @1
    @20
    @27
    @19
    cD
    cF
    cX
    vb
    cF
    va
    crp
    @8
    cmpt
    #
    crn
    vb
    crp
    @25
    cmpt
    #
    crn
    metust.1
    @32
    @33
    va
    vb
    crp
    @8
    @25
    @6
    @23
    wceq
    @7
    @24
    @5
    @6
    @23
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    eqtri
    metustel
    biimpar
    syl2anc
    @16
    vp
    vq
    @21
    cA
    @21
    wrel
    @16
    @19
    @19
    relco
    a1i
    @16
    vp
    cv
    #
    vq
    cv
    #
    cop
    #
    @21
    wcel
    #
    @36
    cA
    wcel
    #
    @16
    @37
    wa
    #
    @34
    cX
    wcel
    #
    @35
    cX
    wcel
    #
    wa
    #
    @38
    @39
    @36
    cX
    cX
    cxp
    #
    wcel
    #
    @42
    @16
    @21
    @43
    @36
    @2
    @21
    @43
    wss
    @3
    @14
    @9
    @2
    @21
    @19
    cdm
    #
    @19
    crn
    #
    cxp
    #
    @43
    @19
    @19
    cossxp
    @2
    @47
    @43
    cdm
    #
    @43
    crn
    #
    cxp
    #
    @43
    @1
    @47
    @50
    wss
    #
    @0
    @1
    @19
    @43
    wss
    #
    @51
    @1
    cD
    cdm
    #
    @19
    @43
    cD
    @18
    cnvimass
    @1
    @43
    cxr
    cD
    wf
    #
    @53
    @43
    wceq
    #
    cD
    cX
    psmetf
    #
    @43
    cxr
    cD
    fdm
    syl
    #
    syl5sseq
    #
    @52
    @45
    @48
    wss
    @46
    @49
    wss
    #
    @51
    @19
    @43
    dmss
    @19
    @43
    rnss
    #
    @45
    @48
    @46
    @49
    xpss12
    syl2anc
    syl
    adantl
    @0
    @50
    @43
    wceq
    @1
    @0
    @48
    cX
    @49
    cX
    cX
    cX
    dmxp
    cX
    cX
    rnxp
    #
    xpeq12d
    adantr
    sseqtrd
    syl5ss
    ad3antrrr
    sselda
    @34
    @35
    cX
    cX
    opelxp
    #
    sylib
    @39
    @42
    wa
    @16
    @40
    @41
    @37
    @38
    @16
    @37
    @42
    simpll
    @39
    @40
    @41
    simprl
    @39
    @40
    @41
    simprr
    @16
    @37
    @42
    simplr
    @16
    @40
    @41
    w3a
    #
    @37
    wa
    #
    @34
    @35
    cA
    wbr
    #
    @38
    @64
    @34
    vr
    cv
    #
    @19
    wbr
    #
    @66
    @35
    @19
    wbr
    #
    wa
    #
    @65
    vr
    cX
    @64
    @66
    cX
    wcel
    #
    wa
    #
    @69
    wa
    #
    @65
    @34
    @35
    @8
    wbr
    #
    @72
    @1
    @14
    wa
    #
    @40
    @41
    w3a
    #
    @70
    @67
    @68
    @73
    @72
    @74
    @40
    @41
    @72
    @1
    @14
    @72
    @16
    @1
    @72
    @16
    @40
    @41
    @63
    @37
    @70
    @69
    simplll
    #
    simp1d
    #
    @28
    syl
    @72
    @16
    @14
    @77
    @30
    syl
    jca
    @72
    @16
    @40
    @41
    @76
    simp2d
    @72
    @16
    @40
    @41
    @76
    simp3d
    3jca
    @64
    @70
    @69
    simplr
    @71
    @67
    @68
    simprl
    @71
    @67
    @68
    simprr
    @75
    @70
    wa
    #
    @69
    wa
    #
    cD
    wfun
    #
    @36
    @53
    wcel
    #
    @36
    cD
    cfv
    #
    @7
    wcel
    #
    @73
    @79
    @1
    @80
    @79
    @1
    @14
    @79
    @74
    @40
    @41
    @75
    @70
    @69
    simpll
    #
    simp1d
    #
    simpld
    #
    @1
    @54
    @80
    @56
    @43
    cxr
    cD
    ffun
    syl
    syl
    #
    @79
    @36
    @43
    @53
    @79
    @40
    @41
    @44
    @79
    @74
    @40
    @41
    @84
    simp2d
    #
    @79
    @74
    @40
    @41
    @84
    simp3d
    #
    @62
    sylanbrc
    #
    @79
    @1
    @55
    @86
    @57
    syl
    #
    eleqtrrd
    @79
    cc0
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @82
    cxr
    wcel
    #
    cc0
    @82
    cle
    wbr
    #
    @82
    @6
    clt
    wbr
    #
    @83
    @92
    @79
    0xr
    a1i
    @79
    @6
    @79
    @1
    @14
    @85
    simprd
    #
    rpxrd
    #
    @79
    @43
    cxr
    @36
    cD
    @79
    @1
    @54
    @86
    @56
    syl
    @90
    ffvelrnd
    #
    @79
    cc0
    @34
    @35
    cD
    co
    #
    @82
    cle
    @79
    @1
    @40
    @41
    cc0
    @100
    cle
    wbr
    @86
    @88
    @89
    @34
    @35
    cD
    cX
    psmetge0
    syl3anc
    @34
    @35
    cD
    df-ov
    #
    syl6breq
    @79
    @82
    @100
    @6
    clt
    @101
    @79
    @100
    @34
    @66
    cD
    co
    #
    @66
    @35
    cD
    co
    #
    cxad
    co
    #
    @6
    @79
    @100
    @82
    cxr
    @101
    @99
    syl5eqel
    @79
    @104
    @79
    @104
    @102
    @103
    caddc
    co
    #
    cr
    @79
    @102
    cr
    wcel
    #
    @103
    cr
    wcel
    #
    @104
    @105
    wceq
    @79
    cc0
    cr
    wcel
    #
    @17
    cxr
    wcel
    #
    @102
    @18
    wcel
    #
    @106
    @79
    0red
    #
    @79
    @17
    @79
    @6
    @79
    @6
    @97
    rpred
    #
    rehalfcld
    rexrd
    #
    @79
    @102
    @34
    @66
    cop
    #
    cD
    cfv
    #
    @18
    @34
    @66
    cD
    df-ov
    @79
    @80
    @114
    @53
    wcel
    #
    @114
    @19
    wcel
    #
    @115
    @18
    wcel
    #
    @87
    @79
    @114
    @43
    @53
    @79
    @40
    @70
    @114
    @43
    wcel
    @88
    @75
    @70
    @69
    simplr
    #
    @34
    @66
    cX
    cX
    opelxp
    sylanbrc
    @91
    eleqtrrd
    @79
    @67
    @117
    @78
    @67
    @68
    simprl
    @34
    @66
    @19
    df-br
    sylib
    @80
    @116
    wa
    @118
    @117
    @114
    @18
    cD
    fvimacnv
    biimpar
    syl21anc
    syl5eqel
    #
    @108
    @109
    wa
    #
    @110
    wa
    #
    @106
    cc0
    @102
    cle
    wbr
    #
    @102
    @17
    clt
    wbr
    #
    @121
    @110
    @106
    @123
    @124
    w3a
    cc0
    @17
    @102
    elico2
    biimpa
    #
    simp1d
    syl21anc
    #
    @79
    @108
    @109
    @103
    @18
    wcel
    #
    @107
    @111
    @113
    @79
    @103
    @66
    @35
    cop
    #
    cD
    cfv
    #
    @18
    @66
    @35
    cD
    df-ov
    @79
    @80
    @128
    @53
    wcel
    #
    @128
    @19
    wcel
    #
    @129
    @18
    wcel
    #
    @87
    @79
    @128
    @43
    @53
    @79
    @70
    @41
    @128
    @43
    wcel
    @119
    @89
    @66
    @35
    cX
    cX
    opelxp
    sylanbrc
    @91
    eleqtrrd
    @79
    @68
    @131
    @78
    @67
    @68
    simprr
    @66
    @35
    @19
    df-br
    sylib
    @80
    @130
    wa
    @132
    @131
    @128
    @18
    cD
    fvimacnv
    biimpar
    syl21anc
    syl5eqel
    #
    @121
    @127
    wa
    #
    @107
    cc0
    @103
    cle
    wbr
    #
    @103
    @17
    clt
    wbr
    #
    @121
    @127
    @107
    @135
    @136
    w3a
    cc0
    @17
    @103
    elico2
    biimpa
    #
    simp1d
    syl21anc
    #
    @102
    @103
    rexadd
    syl2anc
    #
    @79
    @102
    @103
    @126
    @138
    readdcld
    eqeltrd
    rexrd
    @98
    @79
    @1
    @40
    @41
    @70
    @100
    @104
    cle
    wbr
    @86
    @88
    @89
    @119
    @34
    @35
    @66
    cD
    cX
    psmettri
    syl13anc
    @79
    @104
    @105
    @6
    clt
    @139
    @79
    @102
    @103
    @6
    @126
    @138
    @112
    @79
    @108
    @109
    @110
    @124
    @111
    @113
    @120
    @122
    @106
    @123
    @124
    @125
    simp3d
    syl21anc
    @79
    @108
    @109
    @127
    @136
    @111
    @113
    @133
    @134
    @107
    @135
    @136
    @137
    simp3d
    syl21anc
    lt2halvesd
    eqbrtrd
    xrlelttrd
    syl5eqbrr
    @92
    @93
    wa
    @83
    @94
    @95
    @96
    w3a
    cc0
    @6
    @82
    elico1
    biimpar
    syl23anc
    @80
    @81
    wa
    #
    @83
    wa
    @36
    @8
    wcel
    #
    @73
    @140
    @83
    @141
    @36
    @7
    cD
    fvimacnv
    biimpa
    @34
    @35
    @8
    df-br
    sylibr
    syl21anc
    syl22anc
    @72
    cA
    @8
    @34
    @35
    @72
    @15
    @9
    @77
    simprd
    breqd
    mpbird
    @64
    @70
    @69
    wa
    #
    vr
    wex
    #
    @69
    vr
    cX
    wrex
    @64
    @69
    vr
    wex
    #
    @143
    @64
    @34
    @35
    @21
    wbr
    #
    @144
    @64
    @37
    @145
    @63
    @37
    simpr
    @34
    @35
    @21
    df-br
    sylibr
    vr
    @34
    @35
    @19
    @19
    vp
    vex
    #
    vq
    vex
    brco
    sylib
    @63
    @144
    @143
    wi
    #
    @37
    @16
    @40
    @147
    @41
    @2
    @147
    @3
    @14
    @9
    @2
    @69
    @142
    vr
    @2
    @69
    @70
    @2
    @69
    @70
    @2
    @67
    @70
    @68
    @2
    @67
    wa
    @46
    cX
    @66
    @2
    @46
    cX
    wss
    @67
    @2
    @46
    @49
    cX
    @2
    @52
    @59
    @1
    @52
    @0
    @58
    adantl
    @60
    syl
    @0
    @49
    cX
    wceq
    @1
    @61
    adantr
    sseqtrd
    adantr
    @67
    @66
    @46
    wcel
    @2
    @34
    @66
    @19
    @146
    vr
    vex
    brelrn
    adantl
    sseldd
    adantrr
    ex
    ancrd
    eximdv
    ad3antrrr
    3ad2ant1
    adantr
    mpd
    @69
    vr
    cX
    df-rex
    sylibr
    r19.29a
    @34
    @35
    cA
    df-br
    sylib
    syl31anc
    mpdan
    ex
    relssdv
    @12
    @22
    vv
    @19
    cF
    @10
    @19
    wceq
    #
    @11
    @21
    cA
    @148
    @10
    @19
    @10
    @19
    @148
    id
    #
    @149
    coeq12d
    sseq1d
    rspcev
    syl2anc
    @2
    @3
    @9
    va
    crp
    wrex
    #
    @1
    @3
    @150
    wb
    @0
    cA
    cD
    cF
    cX
    va
    metust.1
    metustel
    adantl
    biimpa
    r19.29a
end
