include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "csup.mm"
include "cxad.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wceq.mm"
include "cxp.mm"
include "cima.mm"
include "cfv.mm"
include "wa.mm"
include "sseld.mm"
include "anim12d.mm"
include "imp.mm"
include "xaddcl.mm"
include "syl.mm"
include "ralrimivva.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "wf.mm"
include "xaddf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "sylancr.mm"
include "mpbird.mm"
include "eqsstrd.mm"
include "supxrcl.mm"
include "xaddcld.mm"
include "eleq2d.mm"
include "pm5.32i.mm"
include "nfvd.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "supxrub.mm"
include "simprr.mm"
include "sseldd.mm"
include "xle2add.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "fvelima.mm"
include "mpan.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "rexxp.mm"
include "sylib.mm"
include "r19.29d2r.mm"
include "ancom.mm"
include "2rexbii.mm"
include "breq1.mm"
include "biimpa.mm"
include "reximi.mm"
include "19.9d2r.mm"
include "sylbi.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "simplr.mm"
include "cmnf.mm"
include "wne.mm"
include "simpr.mm"
include "xlt2addrd.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfrex.mm"
include "nfan.mm"
include "id.mm"
include "ralrimivw.mm"
include "adantr.mm"
include "simplrr.mm"
include "3anassrs.mm"
include "simp1d.mm"
include "simp-4l.mm"
include "simplrl.mm"
include "simpld.mm"
include "simpllr.mm"
include "simprd.mm"
include "jca32.mm"
include "xlt2add.mm"
include "biimpar.mm"
include "sylan2.mm"
include "syl12anc.mm"
include "simplll.mm"
include "simplr2.mm"
include "supxrlub.mm"
include "syl21anc.mm"
include "simplr3.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "ancoms.mm"
include "reximddv2.mm"
include "ex.mm"
include "reximdva.mm"
include "reximia.mm"
include "19.9d2rf.mm"
include "a1i.mm"
include "elovimad.mm"
include "breq2d.mm"
include "rspcedv.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "supxr2.mm"

theorem xrofsup
  let wph: wff ph
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrofsup.1: |- ( ph -> X C_ RR* )
  assume xrofsup.2: |- ( ph -> Y C_ RR* )
  assume xrofsup.3: |- ( ph -> sup ( X , RR* , < ) =/= -oo )
  assume xrofsup.4: |- ( ph -> sup ( Y , RR* , < ) =/= -oo )
  assume xrofsup.5: |- ( ph -> Z = ( +e " ( X X. Y ) ) )


  assert |- ( ph -> sup ( Z , RR* , < ) = ( sup ( X , RR* , < ) +e sup ( Y , RR* , < ) ) )

  proof
    wph
    cZ
    cxr
    wss
    cX
    cxr
    clt
    csup
    #
    cY
    cxr
    clt
    csup
    #
    cxad
    co
    #
    cxr
    wcel
    vz
    cv
    #
    @2
    cle
    wbr
    #
    vz
    cZ
    wral
    @3
    @2
    clt
    wbr
    #
    @3
    vk
    cv
    #
    clt
    wbr
    #
    vk
    cZ
    wrex
    #
    wi
    #
    vz
    cr
    wral
    cZ
    cxr
    clt
    csup
    @2
    wceq
    wph
    cZ
    cxad
    cX
    cY
    cxp
    #
    cima
    #
    cxr
    xrofsup.5
    wph
    @11
    cxr
    wss
    #
    vu
    cv
    #
    cxad
    cfv
    #
    cxr
    wcel
    #
    vu
    @10
    wral
    #
    wph
    vx
    cv
    #
    vy
    cv
    #
    cxad
    co
    #
    cxr
    wcel
    #
    vy
    cY
    wral
    vx
    cX
    wral
    @16
    wph
    @20
    vx
    vy
    cX
    cY
    wph
    @17
    cX
    wcel
    #
    @18
    cY
    wcel
    #
    wa
    #
    wa
    @17
    cxr
    wcel
    #
    @18
    cxr
    wcel
    #
    wa
    #
    @20
    wph
    @23
    @26
    wph
    @21
    @24
    @22
    @25
    wph
    cX
    cxr
    @17
    xrofsup.1
    sseld
    wph
    cY
    cxr
    @18
    xrofsup.2
    sseld
    anim12d
    imp
    @17
    @18
    xaddcl
    syl
    ralrimivva
    @15
    @20
    vu
    vx
    vy
    cX
    cY
    @13
    @17
    @18
    cop
    #
    wceq
    #
    @14
    @19
    cxr
    @28
    @14
    @27
    cxad
    cfv
    @19
    @13
    @27
    cxad
    fveq2
    @17
    @18
    cxad
    df-ov
    syl6eqr
    #
    eleq1d
    ralxp
    sylibr
    wph
    cxad
    wfun
    #
    @10
    cxad
    cdm
    #
    wss
    #
    @12
    @16
    wb
    cxr
    cxr
    cxp
    #
    cxr
    cxad
    wf
    @30
    xaddf
    @33
    cxr
    cxad
    ffun
    ax-mp
    #
    wph
    @10
    @33
    @31
    wph
    cX
    cxr
    wss
    #
    cY
    cxr
    wss
    #
    @10
    @33
    wss
    xrofsup.1
    xrofsup.2
    cX
    cxr
    cY
    cxr
    xpss12
    syl2anc
    @33
    cxr
    cxad
    xaddf
    fdmi
    syl6sseqr
    #
    vu
    @10
    cxr
    cxad
    funimass4
    sylancr
    mpbird
    eqsstrd
    wph
    @0
    @1
    wph
    @35
    @0
    cxr
    wcel
    #
    xrofsup.1
    cX
    supxrcl
    #
    syl
    #
    wph
    @36
    @1
    cxr
    wcel
    #
    xrofsup.2
    cY
    supxrcl
    #
    syl
    #
    xaddcld
    wph
    @4
    vz
    cZ
    wph
    @3
    cZ
    wcel
    #
    wa
    wph
    @3
    @11
    wcel
    #
    wa
    #
    @4
    wph
    @44
    @45
    wph
    cZ
    @11
    @3
    xrofsup.5
    eleq2d
    pm5.32i
    @46
    @4
    vx
    vy
    cX
    cY
    @46
    @4
    vx
    nfvd
    @46
    @4
    vy
    nfvd
    @46
    @19
    @3
    wceq
    #
    @19
    @2
    cle
    wbr
    #
    wa
    #
    vy
    cY
    wrex
    #
    vx
    cX
    wrex
    #
    @4
    vy
    cY
    wrex
    #
    vx
    cX
    wrex
    @46
    @48
    @47
    wa
    #
    vy
    cY
    wrex
    vx
    cX
    wrex
    @51
    @46
    @48
    @47
    vx
    vy
    cX
    cY
    @46
    @48
    vx
    vy
    cX
    cY
    @46
    @23
    wa
    #
    @17
    @0
    cle
    wbr
    #
    @18
    @1
    cle
    wbr
    #
    @48
    @54
    @35
    @21
    @55
    wph
    @35
    @45
    @23
    xrofsup.1
    ad2antrr
    #
    @46
    @21
    @22
    simprl
    #
    cX
    @17
    supxrub
    syl2anc
    @54
    @36
    @22
    @56
    wph
    @36
    @45
    @23
    xrofsup.2
    ad2antrr
    #
    @46
    @21
    @22
    simprr
    #
    cY
    @18
    supxrub
    syl2anc
    @54
    @24
    @25
    @38
    @41
    @55
    @56
    wa
    @48
    wi
    @54
    cX
    cxr
    @17
    @57
    @58
    sseldd
    @54
    cY
    cxr
    @18
    @59
    @60
    sseldd
    @54
    @35
    @38
    @57
    @39
    syl
    @54
    @36
    @41
    @59
    @42
    syl
    @17
    @18
    @0
    @1
    xle2add
    syl22anc
    mp2and
    ralrimivva
    @46
    @14
    @3
    wceq
    #
    vu
    @10
    wrex
    #
    @47
    vy
    cY
    wrex
    vx
    cX
    wrex
    @45
    @62
    wph
    @30
    @45
    @62
    @34
    vu
    @3
    @10
    cxad
    fvelima
    mpan
    adantl
    @61
    @47
    vu
    vx
    vy
    cX
    cY
    @28
    @14
    @19
    @3
    @29
    eqeq1d
    rexxp
    sylib
    r19.29d2r
    @53
    @49
    vx
    vy
    cX
    cY
    @48
    @47
    ancom
    2rexbii
    sylib
    @50
    @52
    vx
    cX
    @49
    @4
    vy
    cY
    @47
    @48
    @4
    @19
    @3
    @2
    cle
    breq1
    biimpa
    reximi
    reximi
    syl
    19.9d2r
    sylbi
    ralrimiva
    wph
    @9
    vz
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @5
    @8
    @64
    @5
    wa
    #
    @3
    vv
    cv
    #
    vw
    cv
    #
    cxad
    co
    #
    clt
    wbr
    #
    vw
    cY
    wrex
    vv
    cX
    wrex
    #
    @8
    @65
    @35
    @36
    @3
    va
    cv
    #
    vb
    cv
    #
    cxad
    co
    #
    wceq
    #
    @71
    @0
    clt
    wbr
    #
    @72
    @1
    clt
    wbr
    #
    w3a
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    #
    @70
    wph
    @35
    @63
    @5
    xrofsup.1
    ad2antrr
    wph
    @36
    @63
    @5
    xrofsup.2
    ad2antrr
    @65
    @3
    @0
    @1
    va
    vb
    wph
    @63
    @5
    simplr
    wph
    @38
    @63
    @5
    @40
    ad2antrr
    wph
    @41
    @63
    @5
    @43
    ad2antrr
    wph
    @0
    cmnf
    wne
    @63
    @5
    xrofsup.3
    ad2antrr
    wph
    @1
    cmnf
    wne
    @63
    @5
    xrofsup.4
    ad2antrr
    @64
    @5
    simpr
    xlt2addrd
    @35
    @36
    wa
    #
    @79
    wa
    #
    @70
    va
    vb
    cxr
    cxr
    @80
    @79
    vb
    @80
    vb
    nfv
    @78
    vb
    va
    cxr
    vb
    cxr
    nfcv
    @77
    vb
    cxr
    nfre1
    nfrex
    nfan
    @81
    @70
    va
    nfvd
    @81
    @70
    vb
    nfvd
    @81
    @80
    @77
    wa
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    @70
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    @81
    @80
    @77
    va
    vb
    cxr
    cxr
    @80
    @80
    vb
    cxr
    wral
    #
    va
    cxr
    wral
    @79
    @80
    @85
    va
    cxr
    @80
    @80
    vb
    cxr
    @80
    id
    ralrimivw
    ralrimivw
    adantr
    @80
    @79
    simpr
    r19.29d2r
    @83
    @84
    va
    cxr
    @71
    cxr
    wcel
    #
    @82
    @70
    vb
    cxr
    @86
    @72
    cxr
    wcel
    #
    wa
    #
    @82
    @70
    @88
    @82
    wa
    #
    @71
    @66
    clt
    wbr
    #
    @72
    @67
    clt
    wbr
    #
    wa
    #
    @69
    vv
    vw
    cX
    cY
    @89
    @66
    cX
    wcel
    #
    wa
    #
    @67
    cY
    wcel
    #
    wa
    #
    @92
    wa
    #
    @74
    @88
    @66
    cxr
    wcel
    #
    @67
    cxr
    wcel
    #
    wa
    wa
    #
    @92
    @69
    @97
    @74
    @75
    @76
    @89
    @93
    @95
    @92
    @77
    @88
    @80
    @77
    @93
    @95
    @92
    w3a
    #
    simplrr
    3anassrs
    simp1d
    @97
    @88
    @98
    @99
    @88
    @82
    @93
    @95
    @92
    simp-4l
    @97
    cX
    cxr
    @66
    @97
    @35
    @36
    @89
    @93
    @95
    @92
    @80
    @88
    @80
    @77
    @101
    simplrl
    3anassrs
    #
    simpld
    @89
    @93
    @95
    @92
    simpllr
    sseldd
    @97
    cY
    cxr
    @67
    @97
    @35
    @36
    @102
    simprd
    @94
    @95
    @92
    simplr
    sseldd
    jca32
    @96
    @92
    simpr
    @100
    @92
    wa
    @74
    @73
    @68
    clt
    wbr
    #
    @69
    @100
    @92
    @103
    @71
    @72
    @66
    @67
    xlt2add
    imp
    @74
    @69
    @103
    @3
    @73
    @68
    clt
    breq1
    biimpar
    sylan2
    syl12anc
    @82
    @88
    @92
    vw
    cY
    wrex
    vv
    cX
    wrex
    #
    @82
    @88
    wa
    #
    @90
    vv
    cX
    wrex
    #
    @91
    vw
    cY
    wrex
    #
    @104
    @105
    @35
    @86
    @75
    @106
    @35
    @36
    @77
    @88
    simplll
    @82
    @86
    @87
    simprl
    @74
    @75
    @76
    @80
    @88
    simplr2
    @35
    @86
    wa
    @75
    @106
    vv
    cX
    @71
    supxrlub
    biimpa
    syl21anc
    @105
    @36
    @87
    @76
    @107
    @35
    @36
    @77
    @88
    simpllr
    @82
    @86
    @87
    simprr
    @74
    @75
    @76
    @80
    @88
    simplr3
    @36
    @87
    wa
    @76
    @107
    vw
    cY
    @72
    supxrlub
    biimpa
    syl21anc
    @90
    @91
    vv
    vw
    cX
    cY
    reeanv
    sylanbrc
    ancoms
    reximddv2
    ex
    reximdva
    reximia
    syl
    19.9d2rf
    syl21anc
    wph
    @70
    @8
    wi
    @63
    @5
    wph
    @69
    @8
    vv
    vw
    cX
    cY
    wph
    @93
    @95
    wa
    #
    wa
    #
    @7
    @69
    vk
    @68
    cZ
    @109
    @68
    cZ
    wcel
    #
    @68
    @11
    wcel
    #
    @109
    @66
    @67
    cX
    cY
    cxad
    wph
    @93
    @95
    simprl
    wph
    @93
    @95
    simprr
    @30
    @109
    @34
    a1i
    wph
    @32
    @108
    @37
    adantr
    elovimad
    wph
    @110
    @111
    wb
    @108
    wph
    cZ
    @11
    @68
    xrofsup.5
    eleq2d
    adantr
    mpbird
    @109
    @6
    @68
    wceq
    #
    wa
    @6
    @68
    @3
    clt
    @109
    @112
    simpr
    breq2d
    rspcedv
    rexlimdvva
    ad2antrr
    mpd
    ex
    ralrimiva
    vz
    vk
    cZ
    @2
    supxr2
    syl22anc
end
