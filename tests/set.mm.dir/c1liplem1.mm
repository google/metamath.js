include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cle.mm"
include "wi.mm"
include "cicc.mm"
include "wral.mm"
include "cdv.mm"
include "cima.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "crn.mm"
include "imassrn.mm"
include "cc.mm"
include "wf.mm"
include "absf.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "a1i.mm"
include "wfun.mm"
include "cdm.mm"
include "dvf.mm"
include "ffun.mm"
include "cres.mm"
include "wceq.mm"
include "ccncf.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "ssdmres.mm"
include "sylibr.mm"
include "cxr.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "wa.mm"
include "funfvima2.mm"
include "imp.mm"
include "syl21anc.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "mp2an.mm"
include "ne0i.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "sseldi.mm"
include "cniccbdd.mm"
include "fvelima.mm"
include "mpan.mm"
include "fvres.mm"
include "adantl.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspccva.mm"
include "eqbrtrrd.mm"
include "adantll.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "breq1.mm"
include "ralrimiv.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "suprcl.mm"
include "syl5eqel.mm"
include "cdiv.mm"
include "simplrr.mm"
include "syl.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "eqeltrrd.mm"
include "simplrl.mm"
include "subcld.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "resubcld.mm"
include "crp.mm"
include "simpr.mm"
include "wb.mm"
include "difrp.mm"
include "mpbid.mm"
include "rpne0d.mm"
include "absdivd.mm"
include "divcld.mm"
include "syl6eleqr.mm"
include "ltled.mm"
include "ubicc2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "cioo.mm"
include "iccss2.mm"
include "ad2antlr.mm"
include "resabs1d.mm"
include "rescncf.mm"
include "sylc.mm"
include "ctg.mm"
include "cnt.mm"
include "cpm.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2.mm"
include "simplbi.mm"
include "simprbi.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "iccntr.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "ioossicc.mm"
include "syl5ss.mm"
include "sstrd.mm"
include "sylib.mm"
include "mvth.mm"
include "fveq1d.mm"
include "adantrr.mm"
include "ad2antll.mm"
include "sseld.mm"
include "impr.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "expr.mm"
include "rexlimdv.mm"
include "funfvima.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "abscld.mm"
include "absrpcld.mm"
include "ledivmuld.mm"
include "rpcnd.mm"
include "mulcomd.mm"
include "breqtrd.mm"
include "ralrimivva.mm"
include "jca.mm"

theorem c1liplem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let va: setvar a
  let vb: setvar b
  assume c1liplem1.a: |- ( ph -> A e. RR )
  assume c1liplem1.b: |- ( ph -> B e. RR )
  assume c1liplem1.le: |- ( ph -> A <_ B )
  assume c1liplem1.f: |- ( ph -> F e. ( CC ^pm RR ) )
  assume c1liplem1.dv: |- ( ph -> ( ( RR _D F ) |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) )
  assume c1liplem1.cn: |- ( ph -> ( F |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) )
  assume c1liplem1.k: |- K = sup ( ( abs " ( ( RR _D F ) " ( A [,] B ) ) ) , RR , < )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint b ph
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  assert |- ( ph -> ( K e. RR /\ A. x e. ( A [,] B ) A. y e. ( A [,] B ) ( x < y -> ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_ ( K x. ( abs ` ( y - x ) ) ) ) ) )

  proof
    wph
    cK
    cr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @2
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cK
    @2
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vy
    cA
    cB
    cicc
    co
    #
    wral
    vx
    @13
    wral
    wph
    cK
    cabs
    cr
    cF
    cdv
    co
    #
    @13
    cima
    #
    cima
    #
    cr
    clt
    csup
    #
    cr
    c1liplem1.k
    wph
    @16
    cr
    wss
    #
    @16
    c0
    wne
    #
    vb
    cv
    #
    va
    cv
    #
    cle
    wbr
    #
    vb
    @16
    wral
    #
    va
    cr
    wrex
    #
    @17
    cr
    wcel
    @18
    wph
    @16
    cabs
    crn
    #
    cr
    cabs
    @15
    imassrn
    cc
    cr
    cabs
    wf
    #
    @25
    cr
    wss
    absf
    cc
    cr
    cabs
    frn
    ax-mp
    sstri
    #
    a1i
    wph
    cA
    @14
    cfv
    #
    @15
    wcel
    #
    @28
    cabs
    cfv
    #
    @16
    wcel
    #
    @19
    wph
    @14
    wfun
    #
    @13
    @14
    cdm
    #
    wss
    #
    cA
    @13
    wcel
    #
    @29
    @32
    wph
    @33
    cc
    @14
    wf
    #
    @32
    cF
    dvf
    #
    @33
    cc
    @14
    ffun
    ax-mp
    #
    a1i
    wph
    @14
    @13
    cres
    #
    cdm
    @13
    wceq
    #
    @34
    wph
    @39
    @13
    cr
    ccncf
    co
    #
    wcel
    @13
    cr
    @39
    wf
    @40
    c1liplem1.dv
    @13
    cr
    @39
    cncff
    @13
    cr
    @39
    fdm
    3syl
    @13
    @14
    ssdmres
    sylibr
    #
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @35
    wph
    cA
    c1liplem1.a
    rexrd
    wph
    cB
    c1liplem1.b
    rexrd
    c1liplem1.le
    cA
    cB
    lbicc2
    syl3anc
    @32
    @34
    wa
    #
    @35
    @29
    @13
    cA
    @14
    funfvima2
    imp
    syl21anc
    cabs
    wfun
    #
    @15
    cabs
    cdm
    #
    wss
    @29
    @31
    wi
    @26
    @44
    absf
    cc
    cr
    cabs
    ffun
    ax-mp
    #
    @15
    cc
    @45
    @15
    @14
    crn
    #
    cc
    @14
    @13
    imassrn
    @36
    @47
    cc
    wss
    @37
    @33
    cc
    @14
    frn
    ax-mp
    sstri
    cc
    cr
    cabs
    absf
    fdmi
    #
    sseqtr4i
    @15
    @28
    cabs
    funfvima2
    mp2an
    @16
    @30
    ne0i
    3syl
    #
    wph
    @1
    @39
    cfv
    #
    cabs
    cfv
    #
    @21
    cle
    wbr
    #
    vx
    @13
    wral
    #
    va
    cr
    wrex
    #
    @24
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @39
    @13
    cc
    ccncf
    co
    #
    wcel
    @54
    c1liplem1.a
    c1liplem1.b
    wph
    @41
    @57
    @39
    cr
    cc
    wss
    #
    cc
    cc
    wss
    @41
    @57
    wss
    ax-resscn
    cc
    ssid
    @13
    cr
    cc
    cncfss
    mp2an
    c1liplem1.dv
    sseldi
    va
    vx
    cA
    cB
    @39
    cniccbdd
    syl3anc
    wph
    @53
    @23
    va
    cr
    wph
    @21
    cr
    wcel
    wa
    #
    @53
    @23
    @59
    @53
    wa
    #
    @22
    vb
    @16
    @20
    @16
    wcel
    #
    @2
    cabs
    cfv
    #
    @20
    wceq
    #
    vy
    @15
    wrex
    #
    @60
    @22
    @44
    @61
    @64
    @46
    vy
    @20
    @15
    cabs
    fvelima
    mpan
    @60
    @63
    @22
    vy
    @15
    @60
    @2
    @15
    wcel
    #
    wa
    @62
    @21
    cle
    wbr
    #
    @63
    @22
    @60
    @65
    @66
    @65
    @20
    @14
    cfv
    #
    @2
    wceq
    #
    vb
    @13
    wrex
    #
    @60
    @66
    @32
    @65
    @69
    @38
    vb
    @2
    @13
    @14
    fvelima
    mpan
    @60
    @68
    @66
    vb
    @13
    @60
    @20
    @13
    wcel
    #
    wa
    @67
    cabs
    cfv
    #
    @21
    cle
    wbr
    #
    @68
    @66
    @53
    @70
    @72
    @59
    @53
    @70
    wa
    #
    @20
    @39
    cfv
    #
    cabs
    cfv
    #
    @71
    @21
    cle
    @73
    @74
    @67
    cabs
    @70
    @74
    @67
    wceq
    @53
    @20
    @13
    @14
    fvres
    adantl
    fveq2d
    @52
    @75
    @21
    cle
    wbr
    vx
    @20
    @13
    @1
    @20
    wceq
    #
    @51
    @75
    @21
    cle
    @76
    @50
    @74
    cabs
    @1
    @20
    @39
    fveq2
    fveq2d
    breq1d
    rspccva
    eqbrtrrd
    adantll
    @68
    @71
    @62
    @21
    cle
    @67
    @2
    cabs
    fveq2
    breq1d
    syl5ibcom
    rexlimdva
    syl5
    imp
    @62
    @20
    @21
    cle
    breq1
    syl5ibcom
    rexlimdva
    syl5
    ralrimiv
    ex
    reximdva
    mpd
    #
    va
    vb
    @16
    suprcl
    syl3anc
    syl5eqel
    #
    wph
    @12
    vx
    vy
    @13
    @13
    wph
    @1
    @13
    wcel
    #
    @2
    @13
    wcel
    #
    wa
    #
    wa
    #
    @3
    @11
    @82
    @3
    wa
    #
    @7
    @9
    cK
    cmul
    co
    #
    @10
    cle
    @83
    @7
    @9
    cdiv
    co
    #
    cK
    cle
    wbr
    @7
    @84
    cle
    wbr
    @83
    @6
    @8
    cdiv
    co
    #
    cabs
    cfv
    #
    @85
    cK
    cle
    @83
    @6
    @8
    @83
    @4
    @5
    @83
    @2
    cF
    @13
    cres
    #
    cfv
    #
    @4
    cc
    @83
    @80
    @89
    @4
    wceq
    wph
    @79
    @80
    @3
    simplrr
    #
    @2
    @13
    cF
    fvres
    syl
    @83
    @89
    @83
    @13
    cr
    @2
    @88
    wph
    @13
    cr
    @88
    wf
    #
    @81
    @3
    wph
    @88
    @41
    wcel
    #
    @91
    c1liplem1.cn
    @13
    cr
    @88
    cncff
    syl
    ad2antrr
    #
    @90
    ffvelrnd
    recnd
    eqeltrrd
    @83
    @1
    @88
    cfv
    #
    @5
    cc
    @83
    @79
    @94
    @5
    wceq
    wph
    @79
    @80
    @3
    simplrl
    #
    @1
    @13
    cF
    fvres
    syl
    @83
    @94
    @83
    @13
    cr
    @1
    @88
    @93
    @95
    ffvelrnd
    recnd
    eqeltrrd
    subcld
    #
    @83
    @8
    @83
    @2
    @1
    @83
    @13
    cr
    @2
    wph
    @13
    cr
    wss
    #
    @81
    @3
    wph
    @55
    @56
    @97
    c1liplem1.a
    c1liplem1.b
    cA
    cB
    iccssre
    syl2anc
    ad2antrr
    #
    @90
    sseldd
    #
    @83
    @13
    cr
    @1
    @98
    @95
    sseldd
    #
    resubcld
    recnd
    #
    @83
    @8
    @83
    @3
    @8
    crp
    wcel
    #
    @82
    @3
    simpr
    #
    @83
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @3
    @102
    wb
    @100
    @99
    @1
    @2
    difrp
    syl2anc
    mpbid
    rpne0d
    #
    absdivd
    @83
    @87
    @17
    cK
    cle
    @83
    @18
    @19
    @24
    @87
    @16
    wcel
    #
    @87
    @17
    cle
    wbr
    @18
    @83
    @27
    a1i
    wph
    @19
    @81
    @3
    @49
    ad2antrr
    wph
    @24
    @81
    @3
    @77
    ad2antrr
    @83
    @44
    @86
    @45
    wcel
    #
    @86
    @15
    wcel
    #
    @107
    @44
    @83
    @46
    a1i
    @83
    @86
    cc
    @45
    @83
    @6
    @8
    @96
    @101
    @106
    divcld
    @48
    syl6eleqr
    @83
    @2
    cF
    @1
    @2
    cicc
    co
    #
    cres
    #
    cfv
    #
    @1
    @111
    cfv
    #
    cmin
    co
    #
    @8
    cdiv
    co
    #
    @86
    @15
    @83
    @114
    @6
    @8
    cdiv
    @83
    @112
    @4
    @113
    @5
    cmin
    @83
    @2
    @110
    wcel
    #
    @112
    @4
    wceq
    @83
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    @1
    @2
    cle
    wbr
    #
    @116
    @83
    @1
    @100
    rexrd
    #
    @83
    @2
    @99
    rexrd
    #
    @83
    @1
    @2
    @100
    @99
    @103
    ltled
    #
    @1
    @2
    ubicc2
    syl3anc
    @2
    @110
    cF
    fvres
    syl
    @83
    @1
    @110
    wcel
    #
    @113
    @5
    wceq
    @83
    @117
    @118
    @119
    @123
    @120
    @121
    @122
    @1
    @2
    lbicc2
    syl3anc
    @1
    @110
    cF
    fvres
    syl
    oveq12d
    oveq1d
    @83
    @21
    cr
    @111
    cdv
    co
    #
    cfv
    #
    @115
    wceq
    #
    va
    @1
    @2
    cioo
    co
    #
    wrex
    @115
    @15
    wcel
    #
    @83
    va
    @1
    @2
    @111
    @100
    @99
    @103
    @83
    @88
    @110
    cres
    #
    @111
    @110
    cr
    ccncf
    co
    #
    @83
    cF
    @110
    @13
    @81
    @110
    @13
    wss
    #
    wph
    @3
    cA
    cB
    @1
    @2
    iccss2
    ad2antlr
    #
    resabs1d
    @83
    @131
    @92
    @129
    @130
    wcel
    @132
    wph
    @92
    @81
    @3
    c1liplem1.cn
    ad2antrr
    @13
    cr
    @110
    @88
    rescncf
    sylc
    eqeltrrd
    @83
    @124
    cdm
    @14
    @127
    cres
    #
    cdm
    #
    @127
    @83
    @124
    @133
    @83
    @124
    @14
    @110
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @133
    @83
    @58
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @138
    cr
    wss
    #
    @110
    cr
    wss
    #
    @124
    @137
    wceq
    @58
    @83
    ax-resscn
    a1i
    @83
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    @139
    wph
    @142
    @81
    @3
    c1liplem1.f
    ad2antrr
    #
    @142
    @139
    @140
    cc
    cr
    cF
    cnex
    reex
    elpm2
    #
    simplbi
    syl
    @83
    @142
    @140
    @143
    @142
    @139
    @140
    @144
    simprbi
    syl
    @83
    @104
    @105
    @141
    @100
    @99
    @1
    @2
    iccssre
    syl2anc
    @138
    @110
    cr
    @135
    cF
    ccnfld
    ctopn
    cfv
    #
    @145
    eqid
    #
    @145
    @146
    tgioo2
    dvres
    syl22anc
    @83
    @136
    @127
    @14
    @83
    @104
    @105
    @136
    @127
    wceq
    @100
    @99
    @1
    @2
    iccntr
    syl2anc
    reseq2d
    eqtrd
    #
    dmeqd
    @83
    @127
    @33
    wss
    @134
    @127
    wceq
    @83
    @127
    @13
    @33
    @83
    @127
    @110
    @13
    @1
    @2
    ioossicc
    @132
    syl5ss
    #
    wph
    @34
    @81
    @3
    @42
    ad2antrr
    sstrd
    @127
    @14
    ssdmres
    sylib
    eqtrd
    mvth
    @83
    @126
    @128
    va
    @127
    @82
    @3
    @21
    @127
    wcel
    #
    @126
    @128
    wi
    @82
    @3
    @149
    wa
    #
    wa
    #
    @125
    @15
    wcel
    @126
    @128
    @151
    @125
    @21
    @14
    cfv
    #
    @15
    @151
    @125
    @21
    @133
    cfv
    #
    @152
    @82
    @3
    @125
    @153
    wceq
    @149
    @83
    @21
    @124
    @133
    @147
    fveq1d
    adantrr
    @149
    @153
    @152
    wceq
    @82
    @3
    @21
    @127
    @14
    fvres
    ad2antll
    eqtrd
    @151
    @32
    @34
    @21
    @13
    wcel
    #
    @152
    @15
    wcel
    #
    @32
    @151
    @38
    a1i
    wph
    @34
    @81
    @150
    @42
    ad2antrr
    @82
    @3
    @149
    @154
    @83
    @127
    @13
    @21
    @148
    sseld
    impr
    @43
    @154
    @155
    @13
    @21
    @14
    funfvima2
    imp
    syl21anc
    eqeltrd
    @125
    @115
    @15
    eleq1
    syl5ibcom
    expr
    rexlimdv
    mpd
    eqeltrrd
    @44
    @108
    wa
    @109
    @107
    @15
    @86
    cabs
    funfvima
    imp
    syl21anc
    va
    vb
    @16
    @87
    suprub
    syl31anc
    c1liplem1.k
    syl6breqr
    eqbrtrrd
    @83
    @7
    cK
    @9
    @83
    @6
    @96
    abscld
    wph
    @0
    @81
    @3
    @78
    ad2antrr
    #
    @83
    @8
    @101
    @106
    absrpcld
    #
    ledivmuld
    mpbid
    @83
    @9
    cK
    @83
    @9
    @157
    rpcnd
    @83
    cK
    @156
    recnd
    mulcomd
    breqtrd
    ex
    ralrimivva
    jca
end
