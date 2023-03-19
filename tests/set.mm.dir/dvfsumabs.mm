include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "csb.mm"
include "cmin.mm"
include "csu.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "cfn.mm"
include "wcel.mm"
include "fzofi.mm"
include "a1i.mm"
include "wa.mm"
include "cc.mm"
include "cfz.mm"
include "wral.mm"
include "cicc.mm"
include "cz.mm"
include "cin.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzel2.mm"
include "syl.mm"
include "eluzelz.mm"
include "fzval2.mm"
include "syl2anc.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "cmpt.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "fzofzp1.mm"
include "csbeq1.mm"
include "rspccva.mm"
include "syl2an.mm"
include "elfzofz.mm"
include "subcld.mm"
include "fsumsub.mm"
include "cvv.mm"
include "vex.mm"
include "eqeq2.mm"
include "biimpa.mm"
include "csbied.mm"
include "telfsumo2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "fsumcl.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "fsumabs.mm"
include "cmul.mm"
include "wbr.mm"
include "cxr.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "zred.mm"
include "rexrd.mm"
include "cr.mm"
include "peano2re.mm"
include "lep1d.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "lbicc2.mm"
include "cres.mm"
include "wss.mm"
include "adantr.mm"
include "elfzole1.mm"
include "elfzle2.mm"
include "iccss.mm"
include "syl22anc.mm"
include "resmptd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ctx.mm"
include "ccn.mm"
include "subcn.mm"
include "iccssre.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "cncfmptid.mm"
include "sylancl.mm"
include "mulcncf.mm"
include "cncfmpt2f.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "cdv.mm"
include "cdm.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "sstrd.mm"
include "mulcld.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "ovex.mm"
include "syl5ss.mm"
include "1cnd.mm"
include "dvmptid.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "dvmptcmul.mm"
include "mulid1d.mm"
include "mpteq2dv.mm"
include "dvmptsub.mm"
include "iooss1.mm"
include "iooss2.mm"
include "dmeqd.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "anassrs.mm"
include "eqbrtrd.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfov.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "dvlip.mm"
include "ex.mm"
include "mp2and.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fvmptf.mm"
include "recnd.mm"
include "peano2cn.mm"
include "sub4d.mm"
include "pncan2d.mm"
include "subdid.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "3eqtr2rd.mm"
include "abs1.mm"
include "eqtr2d.mm"
include "3brtr4d.mm"
include "fsumle.mm"
include "letrd.mm"
include "eqbrtrrd.mm"

theorem dvfsumabs
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume dvfsumabs.m: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume dvfsumabs.a: |- ( ph -> ( x e. ( M [,] N ) |-> A ) e. ( ( M [,] N ) -cn-> CC ) )
  assume dvfsumabs.v: |- ( ( ph /\ x e. ( M (,) N ) ) -> B e. V )
  assume dvfsumabs.b: |- ( ph -> ( RR _D ( x e. ( M (,) N ) |-> A ) ) = ( x e. ( M (,) N ) |-> B ) )
  assume dvfsumabs.c: |- ( x = M -> A = C )
  assume dvfsumabs.d: |- ( x = N -> A = D )
  assume dvfsumabs.x: |- ( ( ph /\ k e. ( M ..^ N ) ) -> X e. CC )
  assume dvfsumabs.y: |- ( ( ph /\ k e. ( M ..^ N ) ) -> Y e. RR )
  assume dvfsumabs.l: |- ( ( ph /\ ( k e. ( M ..^ N ) /\ x e. ( k (,) ( k + 1 ) ) ) ) -> ( abs ` ( X - B ) ) <_ Y )

  disjoint A k
  disjoint k x
  disjoint M k
  disjoint M x
  disjoint N k
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint X x
  disjoint C x
  disjoint D x
  disjoint V x
  disjoint Y x
  disjoint k y
  disjoint A y
  disjoint x y
  disjoint M y
  disjoint N y
  disjoint ph y
  disjoint X y
  disjoint C y
  disjoint D y
  disjoint Y y
  assert |- ( ph -> ( abs ` ( sum_ k e. ( M ..^ N ) X - ( D - C ) ) ) <_ sum_ k e. ( M ..^ N ) Y )

  proof
    wph
    cM
    cN
    cfzo
    co
    #
    cX
    vx
    vk
    cv
    #
    c1
    caddc
    co
    #
    cA
    csb
    #
    vx
    @1
    cA
    csb
    #
    cmin
    co
    #
    cmin
    co
    #
    vk
    csu
    #
    cabs
    cfv
    #
    @0
    cX
    vk
    csu
    #
    cD
    cC
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    @0
    cY
    vk
    csu
    #
    cle
    wph
    @7
    @11
    cabs
    wph
    @7
    @9
    @0
    @5
    vk
    csu
    #
    cmin
    co
    @11
    wph
    @0
    cX
    @5
    vk
    @0
    cfn
    wcel
    wph
    cM
    cN
    fzofi
    a1i
    #
    dvfsumabs.x
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    @4
    wph
    vx
    vy
    cv
    #
    cA
    csb
    #
    cc
    wcel
    #
    vy
    cM
    cN
    cfz
    co
    #
    wral
    #
    @2
    @20
    wcel
    #
    @3
    cc
    wcel
    #
    @15
    wph
    @19
    vy
    @20
    wph
    @17
    @20
    wcel
    @17
    cM
    cN
    cicc
    co
    #
    wcel
    #
    @19
    wph
    @20
    @24
    @17
    wph
    @20
    @24
    cz
    cin
    #
    @24
    wph
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @20
    @26
    wceq
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @27
    dvfsumabs.m
    cM
    cN
    eluzel2
    syl
    #
    wph
    @29
    @28
    dvfsumabs.m
    cM
    cN
    eluzelz
    syl
    #
    cM
    cN
    fzval2
    syl2anc
    @24
    cz
    inss1
    syl6eqss
    sselda
    wph
    cA
    cc
    wcel
    #
    vx
    @24
    wral
    #
    @25
    @19
    wph
    @24
    cc
    vx
    @24
    cA
    cmpt
    #
    wf
    #
    @33
    wph
    @34
    @24
    cc
    ccncf
    co
    #
    wcel
    #
    @35
    dvfsumabs.a
    @24
    cc
    @34
    cncff
    syl
    vx
    @24
    cc
    cA
    @34
    @34
    eqid
    fmpt
    sylibr
    #
    @32
    @19
    vx
    @17
    @24
    vx
    @18
    cc
    vx
    @17
    cA
    nfcsb1v
    nfel1
    vx
    vy
    weq
    #
    cA
    @18
    cc
    vx
    @17
    cA
    csbeq1a
    eleq1d
    rspc
    mpan9
    syldan
    #
    ralrimiva
    #
    cM
    cN
    @1
    fzofzp1
    #
    @19
    @23
    vy
    @2
    @20
    @17
    @2
    wceq
    @18
    @3
    cc
    vx
    @17
    @2
    cA
    csbeq1
    #
    eleq1d
    rspccva
    syl2an
    #
    wph
    @21
    @1
    @20
    wcel
    @4
    cc
    wcel
    #
    @15
    @41
    @1
    cM
    cN
    elfzofz
    @19
    @45
    vy
    @1
    @20
    vy
    vk
    weq
    @18
    @4
    cc
    vx
    @17
    @1
    cA
    csbeq1
    #
    eleq1d
    rspccva
    syl2an
    #
    subcld
    #
    fsumsub
    wph
    @13
    @10
    @9
    cmin
    wph
    @18
    @4
    @3
    cC
    vk
    vy
    cD
    cM
    cN
    @46
    @43
    @17
    cM
    wceq
    #
    vx
    @17
    cA
    cC
    cvv
    @17
    cvv
    wcel
    #
    @49
    vy
    vex
    #
    a1i
    @49
    @39
    wa
    vx
    cv
    #
    cM
    wceq
    #
    cA
    cC
    wceq
    @49
    @39
    @53
    @17
    cM
    @52
    eqeq2
    biimpa
    dvfsumabs.c
    syl
    csbied
    @17
    cN
    wceq
    #
    vx
    @17
    cA
    cD
    cvv
    @50
    @54
    @51
    a1i
    @54
    @39
    wa
    @52
    cN
    wceq
    #
    cA
    cD
    wceq
    @54
    @39
    @55
    @17
    cN
    @52
    eqeq2
    biimpa
    dvfsumabs.d
    syl
    csbied
    dvfsumabs.m
    @40
    telfsumo2
    oveq2d
    eqtrd
    fveq2d
    wph
    @8
    @0
    @6
    cabs
    cfv
    #
    vk
    csu
    @12
    wph
    @7
    wph
    @0
    @6
    vk
    @14
    @16
    cX
    @5
    dvfsumabs.x
    @48
    subcld
    #
    fsumcl
    abscld
    wph
    @0
    @56
    vk
    @14
    @16
    @6
    @57
    abscld
    #
    fsumrecl
    wph
    @0
    cY
    vk
    @14
    dvfsumabs.y
    fsumrecl
    wph
    @0
    @6
    vk
    @14
    @57
    fsumabs
    wph
    @0
    @56
    cY
    vk
    @14
    @58
    dvfsumabs.y
    @16
    @2
    vx
    @1
    @2
    cicc
    co
    #
    cX
    @52
    cmul
    co
    #
    cA
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    @1
    @62
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cY
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
    @56
    cY
    cle
    @16
    @2
    @59
    wcel
    #
    @1
    @59
    wcel
    #
    @66
    @69
    cle
    wbr
    #
    @16
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
    @70
    @16
    @1
    @16
    @1
    @15
    @1
    cz
    wcel
    wph
    @1
    cM
    cN
    elfzoelz
    adantl
    zred
    #
    rexrd
    #
    @16
    @2
    @16
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @76
    @1
    peano2re
    syl
    #
    rexrd
    #
    @16
    @1
    @76
    lep1d
    #
    @1
    @2
    ubicc2
    syl3anc
    #
    @16
    @73
    @74
    @75
    @71
    @77
    @81
    @82
    @1
    @2
    lbicc2
    syl3anc
    #
    @16
    @70
    @71
    wa
    @72
    @16
    vy
    @1
    @2
    @62
    cY
    @2
    @1
    @76
    @80
    @16
    vx
    @24
    @61
    cmpt
    #
    @59
    cres
    #
    @62
    @59
    cc
    ccncf
    co
    #
    @16
    vx
    @24
    @59
    @61
    @16
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cM
    @1
    cle
    wbr
    #
    @2
    cN
    cle
    wbr
    #
    @59
    @24
    wss
    #
    wph
    @88
    @15
    wph
    cM
    @30
    zred
    #
    adantr
    #
    wph
    @89
    @15
    wph
    cN
    @31
    zred
    #
    adantr
    #
    @15
    @90
    wph
    @1
    cM
    cN
    elfzole1
    adantl
    #
    @16
    @22
    @91
    @15
    @22
    wph
    @42
    adantl
    @2
    cM
    cN
    elfzle2
    syl
    #
    cM
    cN
    @1
    @2
    iccss
    syl22anc
    #
    resmptd
    @16
    @92
    @85
    @36
    wcel
    @86
    @87
    wcel
    @99
    @16
    vx
    @60
    cA
    cmin
    ccnfld
    ctopn
    cfv
    #
    @24
    @100
    eqid
    #
    cmin
    @100
    @100
    ctx
    co
    @100
    ccn
    co
    wcel
    @16
    @100
    @101
    subcn
    a1i
    @16
    vx
    cX
    @52
    @24
    @16
    cX
    cc
    wcel
    #
    @24
    cc
    wss
    #
    cc
    cc
    wss
    #
    vx
    @24
    cX
    cmpt
    @36
    wcel
    dvfsumabs.x
    @16
    @24
    cr
    cc
    wph
    @24
    cr
    wss
    #
    @15
    wph
    @88
    @89
    @105
    @93
    @95
    cM
    cN
    iccssre
    syl2anc
    adantr
    #
    ax-resscn
    syl6ss
    #
    @104
    @16
    cc
    ssid
    #
    a1i
    vx
    cX
    @24
    cc
    cncfmptc
    syl3anc
    @16
    @103
    @104
    vx
    @24
    @52
    cmpt
    @36
    wcel
    @107
    @108
    vx
    @24
    cc
    cncfmptid
    sylancl
    mulcncf
    wph
    @37
    @15
    dvfsumabs.a
    adantr
    cncfmpt2f
    @24
    cc
    @59
    @85
    rescncf
    sylc
    eqeltrrd
    @16
    cr
    @62
    cdv
    co
    #
    cdm
    vx
    @1
    @2
    cioo
    co
    #
    cX
    cB
    cmin
    co
    #
    cmpt
    #
    cdm
    @110
    @16
    @109
    @112
    @16
    @109
    cr
    vx
    @110
    @61
    cmpt
    cdv
    co
    @112
    @16
    vx
    @61
    cr
    cioo
    crn
    ctg
    cfv
    #
    @100
    @59
    @110
    cr
    cc
    wss
    @16
    ax-resscn
    a1i
    #
    @16
    @59
    @24
    cr
    @99
    @106
    sstrd
    @16
    @52
    @59
    wcel
    @52
    @24
    wcel
    #
    @61
    cc
    wcel
    #
    @16
    @59
    @24
    @52
    @99
    sselda
    @16
    @115
    wa
    #
    @60
    cA
    @117
    cX
    @52
    @16
    @102
    @115
    dvfsumabs.x
    adantr
    @16
    @24
    cc
    @52
    @107
    sselda
    mulcld
    #
    wph
    @115
    @32
    @15
    wph
    @32
    vx
    @24
    @38
    r19.21bi
    adantlr
    #
    subcld
    #
    syldan
    @100
    @101
    tgioo2
    #
    @101
    @16
    @78
    @79
    @59
    @113
    cnt
    cfv
    cfv
    @110
    wceq
    @76
    @80
    @1
    @2
    iccntr
    syl2anc
    dvmptntr
    @16
    vx
    @61
    @111
    cr
    @113
    @100
    cvv
    cM
    cN
    cioo
    co
    #
    @110
    cr
    cr
    cc
    cpr
    wcel
    @16
    reelprrecn
    a1i
    #
    @52
    @122
    wcel
    #
    @16
    @115
    @116
    @122
    @24
    @52
    cM
    cN
    ioossicc
    #
    sseli
    #
    @120
    sylan2
    @111
    cvv
    wcel
    #
    @16
    @124
    wa
    #
    cX
    cB
    cmin
    ovex
    #
    a1i
    @16
    vx
    @60
    cX
    cA
    cB
    cr
    cc
    cV
    @122
    @123
    @124
    @16
    @115
    @60
    cc
    wcel
    @126
    @118
    sylan2
    @16
    @102
    @124
    dvfsumabs.x
    adantr
    @16
    cr
    vx
    @122
    @60
    cmpt
    cdv
    co
    vx
    @122
    cX
    c1
    cmul
    co
    #
    cmpt
    vx
    @122
    cX
    cmpt
    @16
    vx
    @52
    c1
    cX
    cr
    cc
    @122
    @123
    @16
    @122
    cc
    @52
    @16
    @122
    @24
    cc
    @125
    @107
    syl5ss
    sselda
    @128
    1cnd
    @16
    vx
    @52
    c1
    cr
    @113
    @100
    cc
    cr
    @122
    @123
    @16
    cr
    cc
    @52
    @114
    sselda
    @16
    @52
    cr
    wcel
    wa
    1cnd
    @16
    vx
    cr
    @123
    dvmptid
    @16
    @122
    @24
    cr
    @125
    @106
    syl5ss
    @121
    @101
    @122
    @113
    wcel
    @16
    cM
    cN
    iooretop
    a1i
    dvmptres
    dvfsumabs.x
    dvmptcmul
    @16
    vx
    @122
    @130
    cX
    @16
    cX
    dvfsumabs.x
    mulid1d
    #
    mpteq2dv
    eqtrd
    @124
    @16
    @115
    @32
    @126
    @119
    sylan2
    wph
    @124
    cB
    cV
    wcel
    @15
    dvfsumabs.v
    adantlr
    wph
    cr
    vx
    @122
    cA
    cmpt
    cdv
    co
    vx
    @122
    cB
    cmpt
    wceq
    @15
    dvfsumabs.b
    adantr
    dvmptsub
    @16
    @110
    cM
    @2
    cioo
    co
    #
    @122
    @16
    cM
    cxr
    wcel
    @90
    @110
    @132
    wss
    @16
    cM
    @94
    rexrd
    @97
    cM
    @1
    @2
    iooss1
    syl2anc
    @16
    cN
    cxr
    wcel
    @91
    @132
    @122
    wss
    @16
    cN
    @96
    rexrd
    @98
    cM
    @2
    cN
    iooss2
    syl2anc
    sstrd
    @121
    @101
    @110
    @113
    wcel
    @16
    @1
    @2
    iooretop
    a1i
    dvmptres
    eqtrd
    #
    dmeqd
    vx
    @110
    @111
    @112
    @129
    @112
    eqid
    #
    dmmpti
    syl6eq
    dvfsumabs.y
    @16
    @52
    @109
    cfv
    #
    cabs
    cfv
    #
    cY
    cle
    wbr
    #
    vx
    @110
    wral
    @17
    @110
    wcel
    @17
    @109
    cfv
    #
    cabs
    cfv
    #
    cY
    cle
    wbr
    #
    @16
    @137
    vx
    @110
    @16
    @52
    @110
    wcel
    #
    wa
    #
    @136
    @111
    cabs
    cfv
    #
    cY
    cle
    @142
    @135
    @111
    cabs
    @142
    @135
    @52
    @112
    cfv
    #
    @111
    @142
    @52
    @109
    @112
    @16
    @109
    @112
    wceq
    @141
    @133
    adantr
    fveq1d
    @142
    @141
    @127
    @144
    @111
    wceq
    @16
    @141
    simpr
    @129
    vx
    @110
    @111
    cvv
    @112
    @134
    fvmpt2
    sylancl
    eqtrd
    fveq2d
    wph
    @15
    @141
    @143
    cY
    cle
    wbr
    dvfsumabs.l
    anassrs
    eqbrtrd
    ralrimiva
    @137
    @140
    vx
    @17
    @110
    vx
    @139
    cY
    cle
    vx
    @138
    cabs
    vx
    cabs
    nfcv
    vx
    @17
    @109
    vx
    cr
    @62
    cdv
    vx
    cr
    nfcv
    vx
    cdv
    nfcv
    vx
    @59
    @61
    nfmpt1
    nfov
    vx
    @17
    nfcv
    nffv
    nffv
    vx
    cle
    nfcv
    vx
    cY
    nfcv
    nfbr
    @39
    @136
    @139
    cY
    cle
    @39
    @135
    @138
    cabs
    @52
    @17
    @109
    fveq2
    fveq2d
    breq1d
    rspc
    mpan9
    dvlip
    ex
    mp2and
    @16
    @6
    @65
    cabs
    @16
    @65
    cX
    @2
    cmul
    co
    #
    @3
    cmin
    co
    #
    cX
    @1
    cmul
    co
    #
    @4
    cmin
    co
    #
    cmin
    co
    @145
    @147
    cmin
    co
    #
    @5
    cmin
    co
    @6
    @16
    @63
    @146
    @64
    @148
    cmin
    @16
    @70
    @146
    cvv
    wcel
    @63
    @146
    wceq
    @83
    @145
    @3
    cmin
    ovex
    vx
    @2
    @61
    @146
    @59
    @62
    cvv
    vx
    @2
    nfcv
    vx
    @145
    @3
    cmin
    vx
    @145
    nfcv
    vx
    cmin
    nfcv
    #
    vx
    @2
    cA
    nfcsb1v
    nfov
    @52
    @2
    wceq
    @60
    @145
    cA
    @3
    cmin
    @52
    @2
    cX
    cmul
    oveq2
    vx
    @2
    cA
    csbeq1a
    oveq12d
    @62
    eqid
    #
    fvmptf
    sylancl
    @16
    @71
    @148
    cc
    wcel
    @64
    @148
    wceq
    @84
    @16
    @147
    @4
    @16
    cX
    @1
    dvfsumabs.x
    @16
    @1
    @76
    recnd
    #
    mulcld
    #
    @47
    subcld
    vx
    @1
    @61
    @148
    @59
    @62
    cc
    vx
    @1
    nfcv
    vx
    @147
    @4
    cmin
    vx
    @147
    nfcv
    @150
    vx
    @1
    cA
    nfcsb1v
    nfov
    vx
    vk
    weq
    @60
    @147
    cA
    @4
    cmin
    @52
    @1
    cX
    cmul
    oveq2
    vx
    @1
    cA
    csbeq1a
    oveq12d
    @151
    fvmptf
    syl2anc
    oveq12d
    @16
    @145
    @147
    @3
    @4
    @16
    cX
    @2
    dvfsumabs.x
    @16
    @1
    cc
    wcel
    @2
    cc
    wcel
    @152
    @1
    peano2cn
    syl
    #
    mulcld
    @153
    @44
    @47
    sub4d
    @16
    @149
    cX
    @5
    cmin
    @16
    cX
    @67
    cmul
    co
    @130
    @149
    cX
    @16
    @67
    c1
    cX
    cmul
    @16
    @1
    c1
    @152
    @16
    1cnd
    pncan2d
    #
    oveq2d
    @16
    cX
    @2
    @1
    dvfsumabs.x
    @154
    @152
    subdid
    @131
    3eqtr3d
    oveq1d
    3eqtr2rd
    fveq2d
    @16
    @69
    cY
    c1
    cmul
    co
    cY
    @16
    @68
    c1
    cY
    cmul
    @16
    @68
    c1
    cabs
    cfv
    c1
    @16
    @67
    c1
    cabs
    @155
    fveq2d
    abs1
    syl6eq
    oveq2d
    @16
    cY
    @16
    cY
    dvfsumabs.y
    recnd
    mulid1d
    eqtr2d
    3brtr4d
    fsumle
    letrd
    eqbrtrrd
end
