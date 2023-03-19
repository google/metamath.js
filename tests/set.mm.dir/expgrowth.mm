include "cdv.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "wceq.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc.mm"
include "wrex.mm"
include "wa.mm"
include "cneg.mm"
include "cc0.mm"
include "caddc.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wss.mm"
include "recnprss.mm"
include "syl.mm"
include "sseld.mm"
include "mulcl.mm"
include "syl6an.mm"
include "imp.mm"
include "negcld.mm"
include "adantr.mm"
include "efcl.mm"
include "adantl.mm"
include "c1.mm"
include "ax-1cn.mm"
include "dvmptid.mm"
include "dvmptcmul.mm"
include "mulid1d.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "dvmptneg.mm"
include "dvef.mm"
include "wfn.mm"
include "wf.mm"
include "eff.mm"
include "ffn.mm"
include "ax-mp.mm"
include "dffn5.mm"
include "mpbi.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "oveq2d.mm"
include "mulcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "mulcom.mm"
include "caofcom.mm"
include "eqtr3d.mm"
include "fconst6g.mm"
include "eqidd.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "cdm.mm"
include "dmeqd.mm"
include "dmmptd.mm"
include "dvmulf.mm"
include "3eqtr4rd.mm"
include "ofmul12.mm"
include "syl22anc.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "sylan9eq.mm"
include "wb.mm"
include "w3a.mm"
include "mulass.mm"
include "caofass.mm"
include "eqeq2d.mm"
include "inidm.mm"
include "off.mm"
include "adddir.mm"
include "caofdir.mm"
include "cmin.mm"
include "ofnegsub.mm"
include "syl3anc.mm"
include "neg1cn.mm"
include "fconst6.mm"
include "ofc12.mm"
include "mulm1d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "ofsubid.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "mpbid.mm"
include "0cnd.mm"
include "mul02.mm"
include "caofid2.mm"
include "0cn.mm"
include "fdmi.mm"
include "syl6eq.mm"
include "dvconstbi.mm"
include "wi.mm"
include "cdiv.mm"
include "cdif.mm"
include "wne.mm"
include "efne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ofdivcan4.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "cvv.mm"
include "vex.mm"
include "ovexd.mm"
include "efneg.mm"
include "mpteq2dva.mm"
include "jca.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "divdiv2.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "div1d.mm"
include "ancoms.mm"
include "an32s.mm"
include "sylibd.mm"
include "reximdva.mm"
include "mpd.mm"
include "ex.mm"
include "simprl.mm"
include "expgrowthi.mm"
include "3impb.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "3ad2ant3.mm"
include "rexlimdv3a.mm"
include "impbid.mm"
include "weq.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "syl5eq.mm"
include "cbvrexv.mm"
include "syl6bb.mm"

theorem expgrowth
  let wph: wff ph
  let vt: setvar t
  let cS: class S
  let cK: class K
  let cY: class Y
  let vc: setvar c
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume expgrowth.s: |- ( ph -> S e. { RR , CC } )
  assume expgrowth.k: |- ( ph -> K e. CC )
  assume expgrowth.y: |- ( ph -> Y : S --> CC )
  assume expgrowth.dy: |- ( ph -> dom ( S _D Y ) = S )

  disjoint c t
  disjoint K c
  disjoint K t
  disjoint S c
  disjoint S t
  disjoint Y c
  disjoint c u
  disjoint c x
  disjoint t u
  disjoint t x
  disjoint u x
  disjoint K u
  disjoint K x
  disjoint S u
  disjoint S x
  disjoint Y x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> ( ( S _D Y ) = ( ( S X. { K } ) oF x. Y ) <-> E. c e. CC Y = ( t e. S |-> ( c x. ( exp ` ( K x. t ) ) ) ) ) )

  proof
    wph
    cS
    cY
    cdv
    co
    #
    cS
    cK
    csn
    cxp
    #
    cY
    cmul
    cof
    #
    co
    #
    wceq
    #
    cY
    vu
    cS
    vx
    cv
    #
    cK
    vu
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    wceq
    #
    vx
    cc
    wrex
    #
    cY
    vt
    cS
    vc
    cv
    #
    cK
    vt
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    wceq
    #
    vc
    cc
    wrex
    wph
    @4
    @12
    wph
    @4
    @12
    wph
    @4
    wa
    #
    cY
    vu
    cS
    @7
    cneg
    #
    ce
    cfv
    #
    cmpt
    #
    @2
    co
    #
    cS
    @5
    csn
    cxp
    #
    wceq
    #
    vx
    cc
    wrex
    #
    @12
    @20
    cS
    @24
    cdv
    co
    #
    cS
    cc0
    csn
    #
    cxp
    #
    wceq
    @27
    @20
    @28
    @30
    @23
    @2
    co
    #
    @30
    @20
    @28
    @3
    cS
    cK
    cneg
    #
    csn
    #
    cxp
    #
    cY
    @2
    co
    #
    caddc
    cof
    #
    co
    #
    @23
    @2
    co
    #
    wceq
    #
    @28
    @31
    wceq
    #
    @20
    @39
    @28
    @3
    @23
    @2
    co
    #
    @35
    @23
    @2
    co
    #
    @36
    co
    #
    wceq
    #
    @20
    @44
    @28
    @41
    @34
    @24
    @2
    co
    #
    @36
    co
    #
    wceq
    #
    wph
    @4
    @28
    @0
    @23
    @2
    co
    #
    @45
    @36
    co
    #
    @46
    wph
    @28
    @48
    cY
    @34
    @23
    @2
    co
    #
    @2
    co
    #
    @36
    co
    #
    @49
    wph
    @48
    cY
    vu
    cS
    @22
    @32
    cmul
    co
    #
    cmpt
    #
    @2
    co
    #
    @36
    co
    @48
    cS
    @23
    cdv
    co
    #
    cY
    @2
    co
    #
    @36
    co
    @52
    @28
    wph
    @55
    @57
    @48
    @36
    wph
    cY
    @56
    @2
    co
    @55
    @57
    wph
    @56
    @54
    cY
    @2
    wph
    vu
    vy
    @21
    @32
    vy
    cv
    #
    ce
    cfv
    #
    @59
    cS
    cc
    @22
    @22
    cc
    cc
    cS
    cc
    expgrowth.s
    cc
    cr
    cc
    cpr
    #
    wcel
    wph
    cnelprrecn
    a1i
    wph
    @6
    cS
    wcel
    #
    wa
    #
    @7
    wph
    @61
    @7
    cc
    wcel
    #
    wph
    cK
    cc
    wcel
    #
    @61
    @6
    cc
    wcel
    #
    @63
    expgrowth.k
    wph
    cS
    cc
    @6
    wph
    cS
    @60
    wcel
    #
    cS
    cc
    wss
    expgrowth.s
    cS
    recnprss
    syl
    sseld
    #
    cK
    @6
    mulcl
    syl6an
    imp
    #
    negcld
    #
    wph
    @32
    cc
    wcel
    #
    @61
    wph
    cK
    expgrowth.k
    negcld
    #
    adantr
    #
    @58
    cc
    wcel
    #
    @59
    cc
    wcel
    wph
    @58
    efcl
    adantl
    #
    @74
    wph
    vu
    @7
    cK
    cS
    cc
    cS
    expgrowth.s
    @68
    wph
    @64
    @61
    expgrowth.k
    adantr
    wph
    cS
    vu
    cS
    @7
    cmpt
    cdv
    co
    vu
    cS
    cK
    c1
    cmul
    co
    #
    cmpt
    vu
    cS
    cK
    cmpt
    wph
    vu
    @6
    c1
    cK
    cS
    cc
    cS
    expgrowth.s
    wph
    @61
    @65
    @67
    imp
    c1
    cc
    wcel
    #
    @62
    ax-1cn
    a1i
    wph
    vu
    cS
    expgrowth.s
    dvmptid
    expgrowth.k
    dvmptcmul
    wph
    vu
    cS
    @75
    cK
    wph
    cK
    expgrowth.k
    mulid1d
    mpteq2dv
    eqtrd
    dvmptneg
    cc
    vy
    cc
    @59
    cmpt
    #
    cdv
    co
    #
    @77
    wceq
    wph
    cc
    ce
    cdv
    co
    ce
    @78
    @77
    dvef
    ce
    @77
    cc
    cdv
    ce
    cc
    wfn
    #
    ce
    @77
    wceq
    cc
    cc
    ce
    wf
    @79
    eff
    cc
    cc
    ce
    ffn
    ax-mp
    vy
    cc
    ce
    dffn5
    mpbi
    #
    oveq2i
    @80
    3eqtr3i
    a1i
    @58
    @21
    ce
    fveq2
    #
    @81
    dvmptco
    #
    oveq2d
    wph
    vx
    vy
    cS
    cmul
    cc
    cY
    @56
    @60
    expgrowth.s
    expgrowth.y
    wph
    cS
    cc
    @56
    wf
    cS
    cc
    @54
    wf
    wph
    vu
    cS
    @53
    cc
    @54
    @62
    @22
    @32
    @62
    @21
    cc
    wcel
    #
    @22
    cc
    wcel
    #
    @69
    @21
    efcl
    #
    syl
    #
    @72
    mulcld
    #
    @54
    eqid
    #
    fmptd
    wph
    cS
    cc
    @56
    @54
    @82
    feq1d
    mpbird
    @5
    cc
    wcel
    #
    @73
    wa
    #
    @5
    @58
    cmul
    co
    #
    @58
    @5
    cmul
    co
    wceq
    wph
    @5
    @58
    mulcom
    adantl
    #
    caofcom
    eqtr3d
    oveq2d
    wph
    @51
    @55
    @48
    @36
    wph
    @50
    @54
    cY
    @2
    wph
    @50
    @23
    @34
    @2
    co
    @54
    wph
    vx
    vy
    cS
    cmul
    cc
    @34
    @23
    @60
    expgrowth.s
    wph
    @70
    cS
    cc
    @34
    wf
    #
    @71
    cS
    @32
    cc
    fconst6g
    syl
    #
    wph
    vu
    cS
    @22
    cc
    @23
    @86
    @23
    eqid
    #
    fmptd
    #
    @92
    caofcom
    wph
    vu
    cS
    @22
    @32
    cmul
    @23
    @34
    @60
    cc
    cc
    expgrowth.s
    @86
    @72
    wph
    @23
    eqidd
    @34
    vu
    cS
    @32
    cmpt
    wceq
    wph
    vu
    cS
    @32
    fconstmpt
    a1i
    offval2
    eqtrd
    oveq2d
    oveq2d
    wph
    cS
    cY
    @23
    cS
    expgrowth.s
    expgrowth.y
    @96
    expgrowth.dy
    wph
    @56
    cdm
    @54
    cdm
    cS
    wph
    @56
    @54
    @82
    dmeqd
    wph
    vu
    @54
    cS
    @53
    cc
    @88
    @87
    dmmptd
    eqtrd
    dvmulf
    3eqtr4rd
    wph
    @51
    @45
    @48
    @36
    wph
    @66
    cS
    cc
    cY
    wf
    #
    @93
    cS
    cc
    @23
    wf
    @51
    @45
    wceq
    expgrowth.s
    expgrowth.y
    @94
    @96
    cS
    cY
    @34
    @23
    @60
    ofmul12
    syl22anc
    oveq2d
    eqtrd
    @4
    @48
    @41
    @45
    @36
    @0
    @3
    @23
    @2
    oveq1
    oveq1d
    sylan9eq
    wph
    @44
    @47
    wb
    @4
    wph
    @43
    @46
    @28
    wph
    @42
    @45
    @41
    @36
    wph
    vx
    vy
    vz
    cS
    cmul
    cmul
    cc
    cmul
    @34
    cY
    @23
    cmul
    @60
    expgrowth.s
    @94
    expgrowth.y
    @96
    @89
    @73
    vz
    cv
    #
    cc
    wcel
    w3a
    #
    @91
    @98
    cmul
    co
    @5
    @58
    @98
    cmul
    co
    #
    cmul
    co
    wceq
    wph
    @5
    @58
    @98
    mulass
    adantl
    #
    caofass
    oveq2d
    eqeq2d
    adantr
    mpbird
    wph
    @39
    @44
    wb
    @4
    wph
    @38
    @43
    @28
    wph
    vx
    vy
    vz
    cS
    caddc
    cc
    cmul
    @23
    @3
    @35
    cc
    caddc
    @60
    expgrowth.s
    @96
    wph
    vx
    vy
    cS
    cS
    cS
    cmul
    cc
    cc
    cc
    @1
    cY
    @60
    @60
    @90
    @91
    cc
    wcel
    wph
    @5
    @58
    mulcl
    adantl
    #
    wph
    @64
    cS
    cc
    @1
    wf
    expgrowth.k
    cS
    cK
    cc
    fconst6g
    syl
    #
    expgrowth.y
    expgrowth.s
    expgrowth.s
    cS
    inidm
    #
    off
    #
    wph
    vx
    vy
    cS
    cS
    cS
    cmul
    cc
    cc
    cc
    @34
    cY
    @60
    @60
    @102
    @94
    expgrowth.y
    expgrowth.s
    expgrowth.s
    @104
    off
    @99
    @5
    @58
    caddc
    co
    @98
    cmul
    co
    @5
    @98
    cmul
    co
    @100
    caddc
    co
    wceq
    wph
    @5
    @58
    @98
    adddir
    adantl
    caofdir
    eqeq2d
    adantr
    mpbird
    wph
    @39
    @40
    wb
    @4
    wph
    @38
    @31
    @28
    wph
    @37
    @30
    @23
    @2
    wph
    @3
    cS
    c1
    cneg
    #
    csn
    cxp
    #
    @3
    @2
    co
    #
    @36
    co
    #
    @3
    @3
    cmin
    cof
    co
    #
    @37
    @30
    wph
    @66
    cS
    cc
    @3
    wf
    #
    @111
    @109
    @110
    wceq
    expgrowth.s
    @105
    @105
    cS
    @3
    @3
    @60
    ofnegsub
    syl3anc
    wph
    @108
    @35
    @3
    @36
    wph
    @107
    @1
    @2
    co
    #
    cY
    @2
    co
    @108
    @35
    wph
    vx
    vy
    vz
    cS
    cmul
    cmul
    cc
    cmul
    @107
    @1
    cY
    cmul
    @60
    expgrowth.s
    cS
    cc
    @107
    wf
    wph
    cS
    @106
    cc
    neg1cn
    fconst6
    a1i
    @103
    expgrowth.y
    @101
    caofass
    wph
    @112
    @34
    cY
    @2
    wph
    @112
    cS
    @106
    cK
    cmul
    co
    #
    csn
    #
    cxp
    @34
    wph
    cS
    @106
    cK
    cmul
    @60
    cc
    cc
    expgrowth.s
    @106
    cc
    wcel
    wph
    neg1cn
    a1i
    expgrowth.k
    ofc12
    wph
    @114
    @33
    cS
    wph
    @113
    @32
    wph
    cK
    expgrowth.k
    mulm1d
    sneqd
    xpeq2d
    eqtrd
    oveq1d
    eqtr3d
    oveq2d
    wph
    @66
    @111
    @110
    @30
    wceq
    expgrowth.s
    @105
    cS
    @3
    @60
    ofsubid
    syl2anc
    3eqtr3d
    oveq1d
    eqeq2d
    adantr
    mpbid
    wph
    @31
    @30
    wceq
    @4
    wph
    vx
    cS
    cc0
    cc0
    cmul
    cc
    @23
    @60
    cc
    cc
    expgrowth.s
    @96
    wph
    0cnd
    #
    @115
    @89
    cc0
    @5
    cmul
    co
    cc0
    wceq
    wph
    @5
    mul02
    adantl
    caofid2
    adantr
    eqtrd
    #
    @20
    cS
    @24
    vx
    wph
    @66
    @4
    expgrowth.s
    adantr
    wph
    cS
    cc
    @24
    wf
    @4
    wph
    vx
    vy
    cS
    cS
    cS
    cmul
    cc
    cc
    cc
    cY
    @23
    @60
    @60
    @102
    expgrowth.y
    @96
    expgrowth.s
    expgrowth.s
    @104
    off
    adantr
    @20
    @28
    cdm
    @30
    cdm
    cS
    @20
    @28
    @30
    @116
    dmeqd
    cS
    cc
    @30
    cS
    cc0
    cc
    0cn
    fconst6
    fdmi
    syl6eq
    dvconstbi
    mpbid
    wph
    @27
    @12
    wi
    @4
    wph
    @26
    @11
    vx
    cc
    wph
    @89
    wa
    #
    @26
    cY
    @25
    @23
    cdiv
    cof
    #
    co
    #
    wceq
    #
    @11
    wph
    @26
    @120
    wi
    @89
    @26
    @24
    @23
    @118
    co
    #
    @119
    wceq
    wph
    @120
    @24
    @25
    @23
    @118
    oveq1
    wph
    @121
    cY
    @119
    wph
    @66
    @97
    cS
    cc
    @29
    cdif
    #
    @23
    wf
    @121
    cY
    wceq
    expgrowth.s
    expgrowth.y
    wph
    vu
    cS
    @22
    @122
    @23
    @62
    @83
    @22
    @122
    wcel
    #
    @69
    @83
    @84
    @22
    cc0
    wne
    @123
    @85
    @21
    efne0
    @22
    cc
    cc0
    eldifsn
    sylanbrc
    syl
    @95
    fmptd
    cS
    cY
    @23
    @60
    ofdivcan4
    syl3anc
    eqeq1d
    syl5ib
    adantr
    @117
    @119
    @10
    cY
    @117
    @119
    vu
    cS
    @5
    c1
    @8
    cdiv
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @10
    wph
    @119
    @126
    wceq
    @89
    wph
    vu
    cS
    @5
    @124
    cdiv
    @25
    @23
    @60
    cvv
    cvv
    expgrowth.s
    @5
    cvv
    wcel
    @62
    vx
    vex
    a1i
    @62
    c1
    @8
    cdiv
    ovexd
    @25
    vu
    cS
    @5
    cmpt
    wceq
    wph
    vu
    cS
    @5
    fconstmpt
    a1i
    wph
    vu
    cS
    @22
    @124
    @62
    @63
    @22
    @124
    wceq
    @68
    @7
    efneg
    syl
    mpteq2dva
    offval2
    adantr
    @117
    vu
    cS
    @125
    @9
    wph
    @61
    @89
    @125
    @9
    wceq
    #
    @89
    @62
    @127
    @89
    @62
    wa
    #
    @125
    @9
    c1
    cdiv
    co
    #
    @9
    @62
    @89
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    wa
    #
    @125
    @129
    wceq
    #
    @62
    @63
    @132
    @68
    @63
    @130
    @131
    @7
    efcl
    #
    @7
    efne0
    jca
    syl
    @89
    @76
    c1
    cc0
    wne
    #
    wa
    @132
    @133
    @76
    @135
    ax-1cn
    ax-1ne0
    pm3.2i
    @5
    c1
    @8
    divdiv2
    mp3an2
    sylan2
    @128
    @9
    @62
    @89
    @130
    @9
    cc
    wcel
    @62
    @63
    @130
    @68
    @134
    syl
    @5
    @8
    mulcl
    sylan2
    div1d
    eqtrd
    ancoms
    an32s
    mpteq2dva
    eqtrd
    eqeq2d
    sylibd
    reximdva
    adantr
    mpd
    ex
    wph
    @11
    @4
    vx
    cc
    wph
    @89
    @11
    w3a
    @4
    cS
    @10
    cdv
    co
    #
    @1
    @10
    @2
    co
    #
    wceq
    #
    wph
    @89
    @11
    @138
    wph
    @89
    @11
    wa
    #
    wa
    vu
    @5
    cS
    cK
    @10
    wph
    @66
    @139
    expgrowth.s
    adantr
    wph
    @64
    @139
    expgrowth.k
    adantr
    wph
    @89
    @11
    simprl
    @10
    eqid
    expgrowthi
    3impb
    @11
    wph
    @4
    @138
    wb
    @89
    @11
    @0
    @136
    @3
    @137
    cY
    @10
    cS
    cdv
    oveq2
    cY
    @10
    @1
    @2
    oveq2
    eqeq12d
    3ad2ant3
    mpbird
    rexlimdv3a
    impbid
    @11
    @19
    vx
    vc
    cc
    vx
    vc
    weq
    #
    @10
    @18
    cY
    @140
    @10
    vt
    cS
    @5
    @16
    cmul
    co
    #
    cmpt
    @18
    vu
    vt
    cS
    @9
    @141
    vu
    vt
    weq
    #
    @8
    @16
    @5
    cmul
    @142
    @7
    @15
    ce
    @6
    @14
    cK
    cmul
    oveq2
    fveq2d
    oveq2d
    cbvmptv
    @140
    vt
    cS
    @141
    @17
    @5
    @13
    @16
    cmul
    oveq1
    mpteq2dv
    syl5eq
    eqeq2d
    cbvrexv
    syl6bb
end
