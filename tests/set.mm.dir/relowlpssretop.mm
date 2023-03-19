include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "relowlssretop.mm"
include "wceq.mm"
include "c2.mm"
include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "2re.mm"
include "1lt2.mm"
include "cv.mm"
include "wa.mm"
include "wsbc.mm"
include "wi.mm"
include "cico.mm"
include "co.mm"
include "cvv.mm"
include "ovex.mm"
include "sbcan.mm"
include "wb.mm"
include "1re.mm"
include "sbcg.mm"
include "ax-mp.mm"
include "csb.mm"
include "sbcbr123.mm"
include "csbvarg.mm"
include "csbconstg.mm"
include "breq12i.mm"
include "breqi.mm"
include "3bitri.mm"
include "anbi12i.mm"
include "bitri.mm"
include "sbceqg.mm"
include "csbov123.mm"
include "oveq123i.mm"
include "eqtri.mm"
include "eqeq12i.mm"
include "wrex.mm"
include "wral.mm"
include "simpr.mm"
include "cle.mm"
include "simpl.mm"
include "leid.mm"
include "jccir.mm"
include "w3a.mm"
include "cxr.mm"
include "rexr.mm"
include "elico2.mm"
include "sylan2.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "mpdan.mm"
include "biimpar.mm"
include "adantr.mm"
include "eleq2.mm"
include "adantl.mm"
include "mpbird.mm"
include "cop.mm"
include "cxp.mm"
include "cima.mm"
include "rexpssxrxp.mm"
include "opelxpi.mm"
include "sseldi.mm"
include "cdm.mm"
include "cpw.mm"
include "df-ico.mm"
include "ixxf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "wfun.mm"
include "crab.mm"
include "mpt2fun.mm"
include "funfvima.mm"
include "mpan.mm"
include "sylbir.mm"
include "sylc.mm"
include "df-ov.mm"
include "3eltr4g.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wfn.mm"
include "wf.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "wal.mm"
include "wex.mm"
include "iooelexlt.mm"
include "df-rex.mm"
include "sylib.mm"
include "a1i.mm"
include "elmpt2cl2.mm"
include "elioore.mm"
include "sylan.mm"
include "simp2.mm"
include "syl6bi.mm"
include "ex.mm"
include "com23.mm"
include "mpdi.mm"
include "rexrd.mm"
include "elicore.mm"
include "xrlenlt.mm"
include "biimpd.mm"
include "con2d.mm"
include "syl2anc.mm"
include "mt2d.mm"
include "intnand.mm"
include "jcad.mm"
include "annim.mm"
include "syl6ib.mm"
include "eximdv.mm"
include "mpd.mm"
include "exnal.mm"
include "dfss2.mm"
include "sylnibr.mm"
include "imnan.mm"
include "mpbi.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "mtbiri.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "notbid.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ralnex.mm"
include "jca.mm"
include "adantlr.mm"
include "an12.mm"
include "anbi2i.mm"
include "rspe.mm"
include "syl.mm"
include "rexnal.mm"
include "exp41.mm"
include "com4l.mm"
include "imp41.mm"
include "cuni.mm"
include "ixxex.mm"
include "imaexg.mm"
include "eqeltri.mm"
include "icoreunrn.mm"
include "unirnioo.mm"
include "eqtr3i.mm"
include "tgss2.mm"
include "mp2an.mm"
include "raleqi.mm"
include "bitr4i.mm"
include "sbcth.mm"
include "sbcimg.mm"
include "sbcel1v.mm"
include "mpbir.mm"
include "mpbiran2.mm"
include "3imtr3i.mm"
include "syl2anbr.mm"
include "eqid.mm"
include "eqsbc3.mm"
include "anbi1i.mm"
include "eqimss.mm"
include "mto.mm"
include "nesymir.mm"
include "df-pss.mm"
include "mpbir2an.mm"

theorem relowlpssretop
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vi: setvar i
  let vo: setvar o
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let vy: setvar y
  assume relowlpssretop.1: |- I = ( [,) " ( RR X. RR ) )


  assert |- ( topGen ` ran (,) ) C. ( topGen ` I )

  proof
    cioo
    crn
    #
    ctg
    cfv
    #
    cI
    ctg
    cfv
    #
    wpss
    @1
    @2
    wss
    @1
    @2
    wne
    cI
    relowlpssretop.1
    relowlssretop
    @2
    @1
    @2
    @1
    wceq
    @2
    @1
    wss
    #
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @3
    wn
    #
    2re
    1lt2
    vc
    cv
    #
    cr
    wcel
    #
    c1
    @7
    clt
    wbr
    #
    wa
    #
    vc
    c2
    wsbc
    #
    @6
    vc
    c2
    wsbc
    #
    @4
    @5
    wa
    #
    @6
    @10
    @6
    wi
    #
    vc
    c2
    wsbc
    #
    @11
    @12
    wi
    #
    @4
    @15
    2re
    @14
    vc
    c2
    cr
    @10
    vi
    cv
    #
    c1
    @7
    cico
    co
    #
    wceq
    #
    wa
    #
    vi
    @18
    wsbc
    #
    @6
    vi
    @18
    wsbc
    #
    @10
    @6
    @20
    @6
    wi
    #
    vi
    @18
    wsbc
    #
    @21
    @22
    wi
    #
    @18
    cvv
    wcel
    #
    @24
    c1
    @7
    cico
    ovex
    #
    @23
    vi
    @18
    cvv
    @10
    @8
    vx
    cv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vx
    c1
    wsbc
    #
    @17
    @28
    @7
    cico
    co
    #
    wceq
    #
    vx
    c1
    wsbc
    #
    @6
    @19
    @31
    @8
    vx
    c1
    wsbc
    #
    @29
    vx
    c1
    wsbc
    #
    wa
    @10
    @8
    @29
    vx
    c1
    sbcan
    @35
    @8
    @36
    @9
    c1
    cr
    wcel
    #
    @35
    @8
    wb
    1re
    @8
    vx
    c1
    cr
    sbcg
    ax-mp
    @36
    vx
    c1
    @28
    csb
    #
    vx
    c1
    @7
    csb
    #
    vx
    c1
    clt
    csb
    #
    wbr
    c1
    @7
    @40
    wbr
    @9
    vx
    c1
    @28
    @7
    clt
    sbcbr123
    @38
    c1
    @39
    @7
    @40
    @37
    @38
    c1
    wceq
    1re
    vx
    c1
    cr
    csbvarg
    ax-mp
    #
    @37
    @39
    @7
    wceq
    1re
    vx
    c1
    @7
    cr
    csbconstg
    ax-mp
    #
    breq12i
    c1
    @7
    @40
    clt
    @37
    @40
    clt
    wceq
    1re
    vx
    c1
    clt
    cr
    csbconstg
    ax-mp
    breqi
    3bitri
    anbi12i
    bitri
    @34
    vx
    c1
    @17
    csb
    #
    vx
    c1
    @32
    csb
    #
    wceq
    #
    @19
    @37
    @34
    @45
    wb
    1re
    vx
    c1
    @17
    @32
    cr
    sbceqg
    ax-mp
    @43
    @17
    @44
    @18
    @37
    @43
    @17
    wceq
    1re
    vx
    c1
    @17
    cr
    csbconstg
    ax-mp
    @44
    @38
    @39
    vx
    c1
    cico
    csb
    #
    co
    @18
    vx
    c1
    @28
    @7
    cico
    csbov123
    @38
    @39
    c1
    @7
    @46
    cico
    @41
    @42
    @37
    @46
    cico
    wceq
    1re
    vx
    c1
    cico
    cr
    csbconstg
    ax-mp
    oveq123i
    eqtri
    eqeq12i
    bitri
    @31
    @34
    wa
    @30
    @33
    wa
    #
    vx
    c1
    wsbc
    #
    @6
    @30
    @33
    vx
    c1
    sbcan
    @47
    @28
    cr
    wcel
    #
    wa
    #
    vx
    c1
    wsbc
    #
    @6
    vx
    c1
    wsbc
    #
    @48
    @6
    @50
    @6
    wi
    #
    vx
    c1
    wsbc
    #
    @51
    @52
    wi
    #
    @37
    @54
    1re
    @53
    vx
    c1
    cr
    @50
    @28
    @17
    wcel
    #
    @28
    vo
    cv
    #
    wcel
    #
    @57
    @17
    wss
    #
    wa
    #
    vo
    @0
    wrex
    #
    wi
    #
    vi
    cI
    wral
    #
    vx
    cr
    wral
    #
    @3
    @50
    @63
    wn
    #
    vx
    cr
    wrex
    #
    @64
    wn
    @50
    @49
    @65
    @66
    @47
    @49
    simpr
    @8
    @29
    @33
    @49
    @65
    @49
    @8
    @29
    @33
    @65
    @49
    @8
    @29
    @33
    @65
    @49
    @8
    wa
    #
    @29
    wa
    #
    @33
    wa
    #
    @62
    wn
    #
    vi
    cI
    wrex
    #
    @65
    @69
    @17
    cI
    wcel
    #
    @70
    wa
    #
    @71
    @69
    @56
    @72
    @61
    wn
    #
    wa
    #
    wa
    #
    @73
    @69
    @56
    @75
    @69
    @56
    @28
    @32
    wcel
    #
    @68
    @77
    @33
    @67
    @77
    @29
    @67
    @49
    @28
    @28
    cle
    wbr
    #
    wa
    #
    @77
    @29
    wb
    @67
    @49
    @78
    @49
    @8
    simpl
    @28
    leid
    jccir
    @67
    @77
    @79
    @29
    @67
    @77
    @49
    @78
    @29
    w3a
    #
    @79
    @29
    wa
    @8
    @49
    @7
    cxr
    wcel
    #
    @77
    @80
    wb
    @7
    rexr
    @28
    @7
    @28
    elico2
    sylan2
    @49
    @78
    @29
    df-3an
    syl6bb
    baibd
    mpdan
    biimpar
    adantr
    @33
    @56
    @77
    wb
    @68
    @17
    @32
    @28
    eleq2
    adantl
    mpbird
    @67
    @33
    @75
    @29
    @67
    @33
    wa
    @72
    @74
    @67
    @33
    @72
    @67
    @72
    @33
    @32
    cI
    wcel
    @67
    @28
    @7
    cop
    #
    cico
    cfv
    #
    cico
    cr
    cr
    cxp
    #
    cima
    #
    @32
    cI
    @67
    @82
    cxr
    cxr
    cxp
    #
    wcel
    #
    @82
    @84
    wcel
    #
    @83
    @85
    wcel
    #
    @67
    @84
    @86
    @82
    rexpssxrxp
    @28
    @7
    cr
    cr
    opelxpi
    #
    sseldi
    @90
    @87
    @82
    cico
    cdm
    #
    wcel
    #
    @88
    @89
    wi
    #
    @91
    @86
    @82
    @86
    cxr
    cpw
    cico
    vx
    vc
    vz
    cle
    clt
    cico
    vx
    vc
    vz
    df-ico
    #
    ixxf
    fdmi
    eleq2i
    cico
    wfun
    @92
    @93
    vx
    vc
    cxr
    cxr
    @28
    vz
    cv
    #
    cle
    wbr
    @95
    @7
    clt
    wbr
    wa
    vz
    cxr
    crab
    #
    cico
    @94
    mpt2fun
    @84
    @82
    cico
    funfvima
    mpan
    sylbir
    sylc
    @28
    @7
    cico
    df-ov
    relowlpssretop.1
    3eltr4g
    @17
    @32
    cI
    eleq1
    syl5ibrcom
    imp
    @33
    @74
    @67
    @33
    @60
    wn
    #
    vo
    @0
    wral
    @74
    @33
    @97
    vo
    @0
    @57
    @0
    wcel
    #
    @33
    @97
    @98
    @57
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wceq
    #
    vb
    cxr
    wrex
    va
    cxr
    wrex
    #
    @33
    @97
    wi
    #
    cioo
    @86
    wfn
    #
    @98
    @103
    wb
    @86
    cr
    cpw
    #
    cioo
    wf
    @105
    ioof
    @86
    @106
    cioo
    ffn
    ax-mp
    va
    vb
    cxr
    cxr
    @57
    cioo
    ovelrn
    ax-mp
    @102
    @104
    va
    vb
    cxr
    cxr
    @102
    @104
    wi
    @99
    cxr
    wcel
    @100
    cxr
    wcel
    wa
    @102
    @97
    @33
    @58
    @57
    @32
    wss
    #
    wa
    #
    wn
    @102
    @108
    @28
    @101
    wcel
    #
    @101
    @32
    wss
    #
    wa
    #
    @109
    @110
    wn
    wi
    @111
    wn
    @109
    vy
    cv
    #
    @101
    wcel
    #
    @112
    @32
    wcel
    #
    wi
    #
    vy
    wal
    #
    @110
    @109
    @115
    wn
    #
    vy
    wex
    #
    @116
    wn
    @109
    @113
    @112
    @28
    clt
    wbr
    #
    wa
    #
    vy
    wex
    #
    @118
    @109
    @119
    vy
    @101
    wrex
    @121
    vy
    @99
    @100
    @28
    iooelexlt
    @119
    vy
    @101
    df-rex
    sylib
    @109
    @120
    @117
    vy
    @109
    @120
    @113
    @114
    wn
    #
    wa
    @117
    @109
    @120
    @113
    @122
    @120
    @113
    wi
    @109
    @113
    @119
    simpl
    a1i
    @109
    @114
    @120
    @109
    @114
    @120
    wn
    @109
    @114
    wa
    #
    @119
    @113
    @123
    @119
    @28
    @112
    cle
    wbr
    #
    @109
    @114
    @124
    @109
    @114
    @81
    @124
    vx
    vc
    cxr
    cxr
    @96
    @28
    @7
    cico
    @112
    @94
    elmpt2cl2
    @109
    @81
    @114
    @124
    @109
    @81
    @114
    @124
    wi
    @109
    @81
    wa
    @114
    @112
    cr
    wcel
    #
    @124
    @112
    @7
    clt
    wbr
    #
    w3a
    #
    @124
    @109
    @49
    @81
    @114
    @127
    wb
    @28
    @99
    @100
    elioore
    #
    @28
    @7
    @112
    elico2
    sylan
    @125
    @124
    @126
    simp2
    syl6bi
    ex
    com23
    mpdi
    imp
    @123
    @28
    cxr
    wcel
    #
    @112
    cxr
    wcel
    #
    @119
    @124
    wn
    wi
    @109
    @129
    @114
    @109
    @28
    @128
    rexrd
    adantr
    @123
    @112
    @109
    @49
    @114
    @125
    @128
    @28
    @7
    @112
    elicore
    sylan
    rexrd
    @129
    @130
    wa
    #
    @124
    @119
    @131
    @124
    @119
    wn
    @28
    @112
    xrlenlt
    biimpd
    con2d
    syl2anc
    mt2d
    intnand
    ex
    con2d
    jcad
    @113
    @114
    annim
    syl6ib
    eximdv
    mpd
    @115
    vy
    exnal
    sylib
    vy
    @101
    @32
    dfss2
    sylnibr
    @109
    @110
    imnan
    mpbi
    @102
    @58
    @109
    @107
    @110
    @57
    @101
    @28
    eleq2
    @57
    @101
    @32
    sseq1
    anbi12d
    mtbiri
    @33
    @60
    @108
    @33
    @59
    @107
    @58
    @17
    @32
    @57
    sseq2
    anbi2d
    notbid
    syl5ibrcom
    a1i
    rexlimivv
    sylbi
    com12
    ralrimiv
    @60
    vo
    @0
    ralnex
    sylib
    adantl
    jca
    adantlr
    jca
    @76
    @72
    @56
    @74
    wa
    #
    wa
    @73
    @56
    @72
    @74
    an12
    @132
    @70
    @72
    @56
    @61
    annim
    anbi2i
    bitri
    sylib
    @70
    vi
    cI
    rspe
    syl
    @62
    vi
    cI
    rexnal
    sylib
    exp41
    com4l
    imp41
    @65
    vx
    cr
    rspe
    syl2anc
    @63
    vx
    cr
    rexnal
    sylib
    @3
    @63
    vx
    cI
    cuni
    #
    wral
    #
    @64
    cI
    cvv
    wcel
    @133
    @0
    cuni
    #
    wceq
    @3
    @134
    wb
    cI
    @85
    cvv
    relowlpssretop.1
    cico
    cvv
    wcel
    @85
    cvv
    wcel
    vm
    vn
    vz
    cle
    clt
    cico
    vm
    vn
    vz
    df-ico
    ixxex
    cico
    @84
    cvv
    imaexg
    ax-mp
    eqeltri
    cr
    @133
    @135
    cI
    relowlpssretop.1
    icoreunrn
    #
    unirnioo
    eqtr3i
    vx
    vi
    vo
    cI
    @0
    cvv
    tgss2
    mp2an
    @63
    vx
    cr
    @133
    @136
    raleqi
    bitr4i
    sylnibr
    sbcth
    ax-mp
    @37
    @54
    @55
    wb
    1re
    @50
    @6
    vx
    c1
    cr
    sbcimg
    ax-mp
    mpbi
    @51
    @48
    @49
    vx
    c1
    wsbc
    #
    @137
    @37
    1re
    vx
    c1
    cr
    sbcel1v
    mpbir
    @47
    @49
    vx
    c1
    sbcan
    mpbiran2
    @37
    @52
    @6
    wb
    1re
    @6
    vx
    c1
    cr
    sbcg
    ax-mp
    3imtr3i
    sylbir
    syl2anbr
    sbcth
    ax-mp
    @26
    @24
    @25
    wb
    @27
    @20
    @6
    vi
    @18
    cvv
    sbcimg
    ax-mp
    mpbi
    @21
    @10
    vi
    @18
    wsbc
    #
    @19
    vi
    @18
    wsbc
    #
    wa
    #
    @10
    @10
    @19
    vi
    @18
    sbcan
    @140
    @10
    @139
    @139
    @18
    @18
    wceq
    #
    @18
    eqid
    @26
    @139
    @141
    wb
    @27
    vi
    @18
    @18
    cvv
    eqsbc3
    ax-mp
    mpbir
    @138
    @10
    @139
    @26
    @138
    @10
    wb
    @27
    @10
    vi
    @18
    cvv
    sbcg
    ax-mp
    anbi1i
    mpbiran2
    bitri
    @26
    @22
    @6
    wb
    @27
    @6
    vi
    @18
    cvv
    sbcg
    ax-mp
    3imtr3i
    sbcth
    ax-mp
    @4
    @15
    @16
    wb
    2re
    @10
    @6
    vc
    c2
    cr
    sbcimg
    ax-mp
    mpbi
    @11
    @8
    vc
    c2
    wsbc
    #
    @9
    vc
    c2
    wsbc
    #
    wa
    @13
    @8
    @9
    vc
    c2
    sbcan
    @142
    @4
    @143
    @5
    vc
    c2
    cr
    sbcel1v
    @143
    vc
    c2
    c1
    csb
    #
    vc
    c2
    @7
    csb
    #
    vc
    c2
    clt
    csb
    #
    wbr
    c1
    c2
    @146
    wbr
    @5
    vc
    c2
    c1
    @7
    clt
    sbcbr123
    @144
    c1
    @145
    c2
    @146
    @4
    @144
    c1
    wceq
    2re
    vc
    c2
    c1
    cr
    csbconstg
    ax-mp
    @4
    @145
    c2
    wceq
    2re
    vc
    c2
    cr
    csbvarg
    ax-mp
    breq12i
    c1
    c2
    @146
    clt
    @4
    @146
    clt
    wceq
    2re
    vc
    c2
    clt
    cr
    csbconstg
    ax-mp
    breqi
    3bitri
    anbi12i
    bitri
    @4
    @12
    @6
    wb
    2re
    @6
    vc
    c2
    cr
    sbcg
    ax-mp
    3imtr3i
    mp2an
    @2
    @1
    eqimss
    mto
    nesymir
    @1
    @2
    df-pss
    mpbir2an
end
