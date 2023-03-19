include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "cr.mm"
include "cdv.mm"
include "cmin.mm"
include "wceq.mm"
include "fveq2.mm"
include "cbvitgv.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "cfz.mm"
include "cmul.mm"
include "ccos.mm"
include "csu.mm"
include "caddc.mm"
include "cpi.mm"
include "cmpt.mm"
include "elioore.mm"
include "adantl.mm"
include "halfre.mm"
include "fzfid.mm"
include "elfzelz.mm"
include "zred.mm"
include "simpl.mm"
include "remulcld.mm"
include "recoscld.mm"
include "fsumrecl.mm"
include "readdcld.mm"
include "pire.mm"
include "cc0.mm"
include "wne.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "redivcld.mm"
include "syl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "cn.mm"
include "cmo.mm"
include "csin.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "dirkertrigeq.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cicc.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "oveq2i.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "recn.mm"
include "halfcld.mm"
include "zcnd.mm"
include "mulcld.mm"
include "sincld.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "divcld.mm"
include "fsumcl.mm"
include "addcld.mm"
include "picn.mm"
include "dvmptid.mm"
include "2cnd.mm"
include "2ne0.mm"
include "dvmptdivc.mm"
include "tgioo2.mm"
include "reopn.mm"
include "ancoms.mm"
include "3adant1.mm"
include "recnd.mm"
include "simpr.mm"
include "coscld.mm"
include "sylan2.mm"
include "cres.mm"
include "wss.mm"
include "ax-resscn.mm"
include "resmpt.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "wf.mm"
include "cdm.mm"
include "fmptd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl5sseqr.mm"
include "dvsinax.mm"
include "dmeqd.mm"
include "sseqtr4d.mm"
include "dvcnre.mm"
include "reseq1d.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "3eqtrd.mm"
include "divcan3d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "dvmptfsum.mm"
include "dvmptadd.mm"
include "iccssred.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptres2.mm"
include "syl5eq.mm"
include "fvmpt2d.mm"
include "3eqtr4d.mm"
include "itgeq2dv.mm"
include "ccncf.mm"
include "ioosscn.mm"
include "halfcn.mm"
include "ssid.mm"
include "constcncfg.mm"
include "coscn.mm"
include "mulc1cncf.mm"
include "cncfmpt1f.mm"
include "cncfmptssg.mm"
include "fsumcncf.mm"
include "addcncf.mm"
include "csn.mm"
include "cdif.mm"
include "cncfmptc.mm"
include "mp3an.mm"
include "difssd.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "divcncf.mm"
include "eqeltrd.mm"
include "cibl.mm"
include "ioossicc.mm"
include "cvol.mm"
include "ioombl.mm"
include "sselda.mm"
include "syl6ss.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "iblss.mm"
include "idcncfg.mm"
include "2cn.mm"
include "sincn.mm"
include "ad2antlr.mm"
include "adantlr.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"
include "ftc2.mm"

theorem dirkeritg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let vs: setvar s
  assume dirkeritg.d: |- D = ( n e. NN |-> ( x e. RR |-> if ( ( x mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. x ) ) / ( ( 2 x. _pi ) x. ( sin ` ( x / 2 ) ) ) ) ) ) )
  assume dirkeritg.n: |- ( ph -> N e. NN )
  assume dirkeritg.f: |- F = ( D ` N )
  assume dirkeritg.a: |- ( ph -> A e. RR )
  assume dirkeritg.b: |- ( ph -> B e. RR )
  assume dirkeritg.aleb: |- ( ph -> A <_ B )
  assume dirkeritg.g: |- G = ( x e. ( A [,] B ) |-> ( ( ( x / 2 ) + sum_ k e. ( 1 ... N ) ( ( sin ` ( k x. x ) ) / k ) ) / _pi ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint F x
  disjoint N k
  disjoint N x
  disjoint k ph
  disjoint n x
  disjoint k x
  disjoint A s
  disjoint k s
  disjoint s x
  disjoint B s
  disjoint F s
  disjoint G s
  disjoint N s
  disjoint ph s
  disjoint n s
  assert |- ( ph -> S. ( A (,) B ) ( F ` x ) _d x = ( ( G ` B ) - ( G ` A ) ) )

  proof
    wph
    vx
    cA
    cB
    cioo
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    citg
    #
    vs
    @0
    vs
    cv
    #
    cF
    cfv
    #
    citg
    #
    vs
    @0
    @4
    cr
    cG
    cdv
    co
    #
    cfv
    #
    citg
    cB
    cG
    cfv
    cA
    cG
    cfv
    cmin
    co
    @3
    @6
    wceq
    wph
    vx
    vs
    @0
    @2
    @5
    @1
    @4
    cF
    fveq2
    cbvitgv
    a1i
    wph
    vs
    @0
    @5
    @8
    wph
    @4
    @0
    wcel
    #
    wa
    #
    @4
    vs
    cr
    c1
    c2
    cdiv
    co
    #
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    @4
    cmul
    co
    #
    ccos
    cfv
    #
    vk
    csu
    #
    caddc
    co
    #
    cpi
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    @18
    @5
    @8
    @10
    @4
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    @20
    @18
    wceq
    @9
    @21
    wph
    @4
    cA
    cB
    elioore
    #
    adantl
    #
    @10
    @21
    @22
    @24
    @21
    @17
    cpi
    @21
    @11
    @16
    @11
    cr
    wcel
    #
    @21
    halfre
    a1i
    @21
    @12
    @15
    vk
    @21
    c1
    cN
    fzfid
    #
    @21
    @13
    @12
    wcel
    #
    wa
    #
    @14
    @28
    @13
    @4
    @27
    @13
    cr
    wcel
    #
    @21
    @27
    @13
    @13
    c1
    cN
    elfzelz
    #
    zred
    #
    adantl
    @21
    @27
    simpl
    remulcld
    recoscld
    #
    fsumrecl
    #
    readdcld
    #
    cpi
    cr
    wcel
    #
    @21
    pire
    a1i
    cpi
    cc0
    wne
    #
    @21
    cpi
    pire
    pipos
    gt0ne0ii
    #
    a1i
    #
    redivcld
    #
    syl
    #
    vs
    cr
    @18
    cr
    @19
    @19
    eqid
    #
    fvmpt2
    syl2anc
    wph
    @5
    @20
    wceq
    @9
    wph
    @4
    cF
    @19
    wph
    cD
    vk
    vn
    cF
    @19
    cN
    vs
    cD
    vn
    cn
    vx
    cr
    @1
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    #
    cc0
    wceq
    #
    c2
    vn
    cv
    #
    cmul
    co
    c1
    caddc
    co
    @42
    cdiv
    co
    #
    @45
    @11
    caddc
    co
    #
    @1
    cmul
    co
    #
    csin
    cfv
    #
    @42
    @1
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    cmpt
    vn
    cn
    vs
    cr
    @4
    @42
    cmo
    co
    #
    cc0
    wceq
    #
    @46
    @47
    @4
    cmul
    co
    #
    csin
    cfv
    #
    @42
    @4
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    cmpt
    dirkeritg.d
    vn
    cn
    @55
    @65
    vx
    vs
    cr
    @54
    @64
    @1
    @4
    wceq
    #
    @44
    @57
    @53
    @63
    @46
    @66
    @43
    @56
    cc0
    @1
    @4
    @42
    cmo
    oveq1
    eqeq1d
    @66
    @49
    @59
    @52
    @62
    cdiv
    @66
    @48
    @58
    csin
    @1
    @4
    @47
    cmul
    oveq2
    fveq2d
    @66
    @51
    @61
    @42
    cmul
    @66
    @50
    @60
    csin
    @1
    @4
    c2
    cdiv
    oveq1
    #
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    cbvmptv
    mpteq2i
    eqtri
    dirkeritg.n
    dirkeritg.f
    @41
    dirkertrigeq
    fveq1d
    adantr
    wph
    vs
    @0
    @18
    @7
    cr
    wph
    @7
    cr
    vs
    cA
    cB
    cicc
    co
    #
    @60
    @12
    @14
    csin
    cfv
    #
    @13
    cdiv
    co
    #
    vk
    csu
    #
    caddc
    co
    #
    cpi
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    vs
    @0
    @18
    cmpt
    #
    cG
    @74
    cr
    cdv
    cG
    vx
    @68
    @50
    @12
    @13
    @1
    cmul
    co
    #
    csin
    cfv
    #
    @13
    cdiv
    co
    #
    vk
    csu
    #
    caddc
    co
    #
    cpi
    cdiv
    co
    #
    cmpt
    @74
    dirkeritg.g
    vx
    vs
    @68
    @81
    @73
    @66
    @80
    @72
    cpi
    cdiv
    @66
    @50
    @60
    @79
    @71
    caddc
    @67
    @66
    @12
    @78
    @70
    vk
    @66
    @77
    @69
    @13
    cdiv
    @66
    @76
    @14
    csin
    @1
    @4
    @13
    cmul
    oveq2
    fveq2d
    oveq1d
    sumeq2sdv
    oveq12d
    oveq1d
    cbvmptv
    eqtri
    #
    oveq2i
    wph
    vs
    @73
    @18
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    cr
    @0
    @68
    cr
    cr
    cc
    cpr
    wcel
    #
    wph
    reelprrecn
    a1i
    #
    @21
    @73
    cc
    wcel
    wph
    @21
    @72
    cpi
    @21
    @60
    @71
    @21
    @4
    @4
    recn
    #
    halfcld
    #
    @21
    @12
    @70
    vk
    @26
    @28
    @69
    @13
    @28
    @14
    @28
    @13
    @4
    @27
    @13
    cc
    wcel
    #
    @21
    @27
    @13
    @30
    zcnd
    #
    adantl
    #
    @21
    @4
    cc
    wcel
    #
    @27
    @87
    adantr
    mulcld
    sincld
    #
    @91
    @27
    @13
    cc0
    wne
    #
    @21
    @27
    @13
    @27
    cc0
    c1
    @13
    @27
    0red
    @27
    1red
    @31
    cc0
    c1
    clt
    wbr
    @27
    0lt1
    a1i
    @13
    c1
    cN
    elfzle1
    ltletrd
    gt0ne0d
    #
    adantl
    divcld
    #
    fsumcl
    #
    addcld
    #
    cpi
    cc
    wcel
    #
    @21
    picn
    a1i
    @38
    divcld
    adantl
    @21
    @22
    wph
    @39
    adantl
    wph
    vs
    @72
    @17
    cpi
    cr
    cr
    cr
    @86
    @21
    @72
    cc
    wcel
    wph
    @98
    adantl
    @21
    @17
    cr
    wcel
    wph
    @34
    adantl
    wph
    vs
    @60
    @11
    @71
    @16
    cr
    cr
    cr
    cr
    @86
    @21
    @60
    cc
    wcel
    wph
    @88
    adantl
    @25
    wph
    @21
    wa
    #
    halfre
    a1i
    wph
    vs
    @4
    c1
    c2
    cr
    cr
    cr
    @86
    @21
    @92
    wph
    @87
    adantl
    @100
    1red
    wph
    vs
    cr
    @86
    dvmptid
    wph
    2cnd
    c2
    cc0
    wne
    #
    wph
    2ne0
    a1i
    dvmptdivc
    @21
    @71
    cc
    wcel
    wph
    @97
    adantl
    @21
    @16
    cr
    wcel
    wph
    @33
    adantl
    wph
    vs
    @70
    @15
    cr
    vk
    @12
    @83
    @84
    cr
    @84
    @84
    eqid
    #
    tgioo2
    #
    @102
    @86
    cr
    @83
    wcel
    wph
    reopn
    a1i
    wph
    c1
    cN
    fzfid
    #
    @27
    @21
    @70
    cc
    wcel
    #
    wph
    @21
    @27
    @105
    @96
    ancoms
    3adant1
    @27
    @21
    @15
    cc
    wcel
    #
    wph
    @27
    @21
    wa
    #
    @15
    @21
    @27
    @15
    cr
    wcel
    @32
    ancoms
    recnd
    #
    3adant1
    @27
    cr
    vs
    cr
    @70
    cmpt
    cdv
    co
    #
    vs
    cr
    @15
    cmpt
    #
    wceq
    wph
    @27
    @109
    vs
    cr
    @13
    @15
    cmul
    co
    #
    @13
    cdiv
    co
    #
    cmpt
    @110
    @27
    vs
    @69
    @111
    @13
    cr
    cc
    cr
    @85
    @27
    reelprrecn
    a1i
    @21
    @27
    @69
    cc
    wcel
    @93
    ancoms
    @21
    @27
    @92
    @111
    cc
    wcel
    #
    @87
    @27
    @92
    wa
    #
    @13
    @15
    @27
    @89
    @92
    @90
    adantr
    #
    @114
    @14
    @114
    @13
    @4
    @115
    @27
    @92
    simpr
    mulcld
    #
    coscld
    mulcld
    #
    sylan2
    @27
    cr
    vs
    cr
    @69
    cmpt
    #
    cdv
    co
    cr
    vs
    cc
    @69
    cmpt
    #
    cr
    cres
    #
    cdv
    co
    #
    cc
    @119
    cdv
    co
    #
    cr
    cres
    #
    vs
    cr
    @111
    cmpt
    #
    @27
    @118
    @120
    cr
    cdv
    @27
    @120
    @118
    cr
    cc
    wss
    #
    @120
    @118
    wceq
    @27
    ax-resscn
    vs
    cc
    cr
    @69
    resmpt
    mp1i
    eqcomd
    oveq2d
    @27
    cc
    cc
    @119
    wf
    cr
    @122
    cdm
    #
    wss
    @121
    @123
    wceq
    @27
    vs
    cc
    @69
    cc
    @119
    @114
    @14
    @116
    sincld
    @119
    eqid
    #
    fmptd
    @27
    cr
    vs
    cc
    @111
    cmpt
    #
    cdm
    #
    @126
    @27
    cc
    cr
    @129
    ax-resscn
    @27
    @113
    vs
    cc
    wral
    @129
    cc
    wceq
    @27
    @113
    vs
    cc
    @117
    ralrimiva
    vs
    cc
    @111
    cc
    dmmptg
    syl
    syl5sseqr
    @27
    @122
    @128
    @27
    @89
    @122
    @128
    wceq
    @90
    vs
    @13
    dvsinax
    syl
    #
    dmeqd
    sseqtr4d
    @119
    dvcnre
    syl2anc
    @27
    @123
    @128
    cr
    cres
    #
    @124
    @27
    @122
    @128
    cr
    @130
    reseq1d
    @125
    @131
    @124
    wceq
    ax-resscn
    vs
    cc
    cr
    @111
    resmpt
    ax-mp
    syl6eq
    3eqtrd
    @90
    @95
    dvmptdivc
    @27
    vs
    cr
    @112
    @15
    @107
    @15
    @13
    @108
    @27
    @89
    @21
    @90
    adantr
    @27
    @94
    @21
    @95
    adantr
    divcan3d
    mpteq2dva
    eqtrd
    adantl
    dvmptfsum
    dvmptadd
    @99
    wph
    picn
    a1i
    @36
    wph
    @37
    a1i
    dvmptdivc
    wph
    cA
    cB
    dirkeritg.a
    dirkeritg.b
    iccssred
    #
    @103
    @102
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @68
    @83
    cnt
    cfv
    cfv
    @0
    wceq
    dirkeritg.a
    dirkeritg.b
    cA
    cB
    iccntr
    syl2anc
    dvmptres2
    syl5eq
    #
    @40
    fvmpt2d
    3eqtr4d
    itgeq2dv
    wph
    vs
    cA
    cB
    cG
    dirkeritg.a
    dirkeritg.b
    dirkeritg.aleb
    wph
    @7
    @75
    @0
    cc
    ccncf
    co
    #
    @135
    wph
    vs
    @17
    cpi
    @0
    wph
    vs
    @11
    @16
    @0
    wph
    vs
    @0
    @11
    cc
    @0
    cc
    wss
    #
    wph
    cA
    cB
    ioosscn
    #
    a1i
    #
    @11
    cc
    wcel
    wph
    halfcn
    a1i
    #
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    #
    constcncfg
    wph
    vs
    @12
    @15
    vk
    @0
    @139
    @104
    @27
    vs
    @0
    @15
    cmpt
    @136
    wcel
    wph
    @27
    vs
    cc
    cc
    @0
    cc
    @15
    vs
    cc
    @15
    cmpt
    #
    @144
    eqid
    @27
    vs
    @14
    ccos
    cc
    ccos
    cc
    cc
    ccncf
    co
    #
    wcel
    @27
    coscn
    a1i
    @27
    @89
    vs
    cc
    @14
    cmpt
    #
    @145
    wcel
    @90
    vs
    @13
    @146
    @146
    eqid
    mulc1cncf
    syl
    #
    cncfmpt1f
    #
    @137
    @27
    @138
    a1i
    @141
    @27
    @142
    a1i
    @9
    @27
    @21
    @106
    @23
    @108
    sylan2
    cncfmptssg
    adantl
    fsumcncf
    addcncf
    wph
    vs
    cc
    cc
    @0
    cc
    cc0
    csn
    #
    cdif
    #
    cpi
    vs
    cc
    cpi
    cmpt
    #
    @151
    eqid
    @151
    @145
    wcel
    #
    wph
    @99
    @141
    @141
    @152
    picn
    @142
    @142
    vs
    cpi
    cc
    cc
    cncfmptc
    mp3an
    a1i
    @139
    wph
    cc
    @149
    difssd
    #
    cpi
    @150
    wcel
    #
    @10
    @154
    @99
    @36
    picn
    @37
    cpi
    cc
    cc0
    eldifsn
    mpbir2an
    #
    a1i
    cncfmptssg
    divcncf
    eqeltrd
    wph
    @7
    @75
    cibl
    @135
    wph
    vs
    @0
    @68
    @18
    cr
    @0
    @68
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    @0
    cvol
    cdm
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @4
    @68
    wcel
    #
    wa
    #
    @17
    cpi
    @157
    @11
    @16
    @25
    @157
    halfre
    a1i
    @157
    @12
    @15
    vk
    @157
    c1
    cN
    fzfid
    @157
    @27
    wa
    #
    @14
    @158
    @13
    @4
    @27
    @29
    @157
    @31
    adantl
    @157
    @21
    @27
    wph
    @68
    cr
    @4
    @132
    sselda
    #
    adantr
    remulcld
    recoscld
    fsumrecl
    #
    readdcld
    @35
    @157
    pire
    a1i
    @36
    @157
    @37
    a1i
    redivcld
    wph
    @133
    @134
    vs
    @68
    @18
    cmpt
    #
    @68
    cc
    ccncf
    co
    #
    wcel
    @161
    cibl
    wcel
    dirkeritg.a
    dirkeritg.b
    wph
    vs
    @17
    cpi
    @68
    wph
    vs
    @11
    @16
    @68
    wph
    vs
    @68
    @11
    cc
    wph
    @68
    cr
    cc
    @132
    ax-resscn
    syl6ss
    #
    @140
    @143
    constcncfg
    wph
    vs
    cc
    cc
    @68
    cc
    @16
    vs
    cc
    @16
    cmpt
    #
    @164
    eqid
    wph
    vs
    @12
    @15
    vk
    cc
    @143
    @104
    @27
    @144
    @145
    wcel
    wph
    @148
    adantl
    fsumcncf
    @163
    @143
    @157
    @16
    @160
    recnd
    cncfmptssg
    addcncf
    wph
    vs
    @68
    cpi
    @150
    @163
    @154
    wph
    @155
    a1i
    @153
    constcncfg
    #
    divcncf
    cA
    cB
    @161
    cniccibl
    syl3anc
    iblss
    eqeltrd
    wph
    cG
    @74
    @162
    @82
    wph
    vs
    @72
    cpi
    @68
    wph
    vs
    @60
    @71
    @68
    wph
    vs
    @4
    c2
    @68
    wph
    vs
    @68
    cc
    @163
    @143
    idcncfg
    wph
    vs
    @68
    c2
    @150
    @163
    c2
    @150
    wcel
    #
    wph
    @166
    c2
    cc
    wcel
    @101
    2cn
    2ne0
    c2
    cc
    cc0
    eldifsn
    mpbir2an
    a1i
    @153
    constcncfg
    divcncf
    wph
    vs
    @12
    @70
    vk
    @68
    @163
    @104
    wph
    @27
    wa
    #
    vs
    @69
    @13
    @68
    @167
    vs
    cc
    cc
    @68
    cc
    @69
    @119
    @127
    @27
    @119
    @145
    wcel
    wph
    @27
    vs
    @14
    csin
    cc
    csin
    @145
    wcel
    @27
    sincn
    a1i
    @147
    cncfmpt1f
    adantl
    wph
    @68
    cc
    wss
    @27
    @163
    adantr
    #
    @141
    @167
    @142
    a1i
    @167
    @156
    wa
    #
    @14
    @169
    @13
    @4
    @27
    @89
    wph
    @156
    @90
    ad2antlr
    wph
    @156
    @92
    @27
    @157
    @4
    @159
    recnd
    adantlr
    mulcld
    sincld
    cncfmptssg
    @167
    vs
    @68
    @13
    @150
    @168
    @27
    @13
    @150
    wcel
    #
    wph
    @27
    @89
    @94
    @170
    @90
    @95
    @13
    cc
    cc0
    eldifsn
    sylanbrc
    adantl
    @167
    cc
    @149
    difssd
    constcncfg
    divcncf
    fsumcncf
    addcncf
    @165
    divcncf
    syl5eqel
    ftc2
    3eqtrd
end
