include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cioo.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "0red.mm"
include "resubcld.mm"
include "rexrd.mm"
include "clt.mm"
include "wbr.mm"
include "posdifd.mm"
include "mpbid.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "cxr.mm"
include "elioore.mm"
include "adantl.mm"
include "readdcld.mm"
include "wceq.mm"
include "recnd.mm"
include "addid1d.mm"
include "eqcomd.mm"
include "0xr.mm"
include "a1i.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "iooltub.mm"
include "pncan3d.mm"
include "breqtrd.mm"
include "eliood.mm"
include "ffvelrnd.mm"
include "cc.mm"
include "wss.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "lptioo1cn.mm"
include "limcrecl.mm"
include "fmptd.mm"
include "cdv.mm"
include "cdm.mm"
include "oveq2i.mm"
include "dmeqd.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "feq1d.mm"
include "mpbird.mm"
include "eqtr2d.mm"
include "eleqtrd.mm"
include "c1.mm"
include "cmul.mm"
include "1red.mm"
include "ffvelrnda.mm"
include "feq2d.mm"
include "crn.mm"
include "ctg.mm"
include "dvmptc.mm"
include "tgioo2.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "recn.mm"
include "dvmptid.mm"
include "dvmptadd.mm"
include "0p1e1.mm"
include "mpteq2i.mm"
include "syl6eq.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "mulid1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "limccl.mm"
include "sseldi.mm"
include "dvmptsub.mm"
include "subid1d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "wne.mm"
include "adantrr.mm"
include "constlimc.mm"
include "idlimc.mm"
include "addlimc.mm"
include "eqeltrd.mm"
include "oveq1d.mm"
include "wn.mm"
include "simplrr.mm"
include "gtned.mm"
include "neneqd.mm"
include "condan.mm"
include "limcco.mm"
include "sublimc.mm"
include "subidd.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3eltr3d.mm"
include "lbioo.mm"
include "cid.mm"
include "cres.mm"
include "mptresid.mm"
include "rneqd.mm"
include "rnresi.mm"
include "syl6req.mm"
include "neleqtrd.mm"
include "csn.mm"
include "0ne1.mm"
include "neii.mm"
include "wb.mm"
include "elsng.mm"
include "mtbiri.mm"
include "c0.mm"
include "ioon0.mm"
include "rnmptc.mm"
include "div1d.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "fvmpt2.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "lhop1.mm"
include "syl6eqr.mm"

theorem fourierdlem61
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cY: class Y
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem61.a: |- ( ph -> A e. RR )
  assume fourierdlem61.b: |- ( ph -> B e. RR )
  assume fourierdlem61.altb: |- ( ph -> A < B )
  assume fourierdlem61.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume fourierdlem61.y: |- ( ph -> Y e. ( F limCC A ) )
  assume fourierdlem61.g: |- G = ( RR _D F )
  assume fourierdlem61.domg: |- ( ph -> dom G = ( A (,) B ) )
  assume fourierdlem61.e: |- ( ph -> E e. ( G limCC A ) )
  assume fourierdlem61.h: |- H = ( s e. ( 0 (,) ( B - A ) ) |-> ( ( ( F ` ( A + s ) ) - Y ) / s ) )
  assume fourierdlem61.n: |- N = ( s e. ( 0 (,) ( B - A ) ) |-> ( ( F ` ( A + s ) ) - Y ) )
  assume fourierdlem61.d: |- D = ( s e. ( 0 (,) ( B - A ) ) |-> s )

  disjoint A s
  disjoint B s
  disjoint D s
  disjoint E s
  disjoint F s
  disjoint G s
  disjoint N s
  disjoint Y s
  disjoint ph s
  disjoint A x
  disjoint s x
  disjoint B x
  disjoint E x
  disjoint F x
  disjoint G x
  disjoint Y x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E e. ( H limCC 0 ) )

  proof
    wph
    cE
    vs
    cc0
    cB
    cA
    cmin
    co
    #
    cioo
    co
    #
    vs
    cv
    #
    cN
    cfv
    #
    @2
    cD
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    climc
    co
    cH
    cc0
    climc
    co
    wph
    vs
    cc0
    @0
    cE
    cN
    cD
    wph
    0red
    #
    wph
    @0
    wph
    cB
    cA
    fourierdlem61.b
    fourierdlem61.a
    resubcld
    #
    rexrd
    #
    wph
    cA
    cB
    clt
    wbr
    cc0
    @0
    clt
    wbr
    #
    fourierdlem61.altb
    wph
    cA
    cB
    fourierdlem61.a
    fourierdlem61.b
    posdifd
    mpbid
    #
    wph
    vs
    @1
    cA
    @2
    caddc
    co
    #
    cF
    cfv
    #
    cY
    cmin
    co
    #
    cr
    cN
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @13
    cY
    @16
    cA
    cB
    cioo
    co
    #
    cr
    @12
    cF
    wph
    @17
    cr
    cF
    wf
    #
    @15
    fourierdlem61.f
    adantr
    @16
    cA
    cB
    @12
    wph
    cA
    cxr
    wcel
    @15
    wph
    cA
    fourierdlem61.a
    rexrd
    adantr
    wph
    cB
    cxr
    wcel
    @15
    wph
    cB
    fourierdlem61.b
    rexrd
    #
    adantr
    @16
    cA
    @2
    wph
    cA
    cr
    wcel
    @15
    fourierdlem61.a
    adantr
    #
    @15
    @2
    cr
    wcel
    #
    wph
    @2
    cc0
    @0
    elioore
    adantl
    #
    readdcld
    @16
    cA
    cA
    cc0
    caddc
    co
    #
    @12
    clt
    wph
    cA
    @23
    wceq
    @15
    wph
    @23
    cA
    wph
    cA
    wph
    cA
    fourierdlem61.a
    recnd
    #
    addid1d
    eqcomd
    #
    adantr
    @16
    cc0
    @2
    cA
    @16
    0red
    #
    @22
    @20
    @16
    cc0
    cxr
    wcel
    #
    @0
    cxr
    wcel
    #
    @15
    cc0
    @2
    clt
    wbr
    @27
    @16
    0xr
    a1i
    #
    wph
    @28
    @15
    @9
    adantr
    #
    wph
    @15
    simpr
    #
    cc0
    @0
    @2
    ioogtlb
    syl3anc
    ltadd2dd
    eqbrtrd
    #
    @16
    @12
    cA
    @0
    caddc
    co
    #
    cB
    clt
    @16
    @2
    @0
    cA
    @22
    wph
    @0
    cr
    wcel
    @15
    @8
    adantr
    @20
    @16
    @27
    @28
    @15
    @2
    @0
    clt
    wbr
    @29
    @30
    @31
    cc0
    @0
    @2
    iooltub
    syl3anc
    ltadd2dd
    wph
    @33
    cB
    wceq
    @15
    wph
    cA
    cB
    @24
    wph
    cB
    fourierdlem61.b
    recnd
    pncan3d
    adantr
    breqtrd
    eliood
    #
    ffvelrnd
    #
    wph
    cY
    cr
    wcel
    @15
    wph
    @17
    cA
    cF
    cY
    fourierdlem61.f
    wph
    @17
    cr
    cc
    @17
    cr
    wss
    #
    wph
    cA
    cB
    ioossre
    a1i
    #
    ax-resscn
    syl6ss
    wph
    cA
    cB
    ccnfld
    ctopn
    cfv
    #
    @38
    eqid
    #
    @19
    fourierdlem61.a
    fourierdlem61.altb
    lptioo1cn
    fourierdlem61.y
    limcrecl
    adantr
    resubcld
    #
    fourierdlem61.n
    fmptd
    wph
    vs
    @1
    @2
    cr
    cD
    @22
    fourierdlem61.d
    fmptd
    wph
    cr
    cN
    cdv
    co
    #
    cdm
    cr
    vs
    @1
    @14
    cmpt
    #
    cdv
    co
    #
    cdm
    vs
    @1
    @12
    cG
    cfv
    #
    cmpt
    #
    cdm
    #
    @1
    wph
    @41
    @43
    @41
    @43
    wceq
    wph
    cN
    @42
    cr
    cdv
    fourierdlem61.n
    oveq2i
    #
    a1i
    dmeqd
    wph
    @43
    @45
    wph
    @43
    vs
    @1
    @44
    cc0
    cmin
    co
    #
    cmpt
    @45
    wph
    vs
    @13
    @44
    cY
    cc0
    cr
    cr
    cxr
    @1
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @16
    @13
    @35
    recnd
    #
    @16
    cr
    cF
    cdv
    co
    #
    cdm
    #
    cr
    @12
    cG
    wph
    @52
    cr
    cG
    wf
    #
    @15
    wph
    @53
    @52
    cr
    @51
    wf
    #
    wph
    @18
    @36
    @54
    fourierdlem61.f
    @37
    @17
    cF
    dvfre
    syl2anc
    wph
    @52
    cr
    cG
    @51
    cG
    @51
    wceq
    wph
    fourierdlem61.g
    a1i
    #
    feq1d
    mpbird
    #
    adantr
    @16
    @12
    @17
    @52
    @34
    wph
    @17
    @52
    wceq
    @15
    wph
    @52
    cG
    cdm
    @17
    wph
    @51
    cG
    wph
    cG
    @51
    @55
    eqcomd
    #
    dmeqd
    fourierdlem61.domg
    eqtr2d
    #
    adantr
    eleqtrd
    ffvelrnd
    #
    wph
    cr
    vs
    @1
    @13
    cmpt
    #
    cdv
    co
    vs
    @1
    @44
    c1
    cmul
    co
    #
    cmpt
    @45
    wph
    vs
    vx
    @12
    c1
    vx
    cv
    #
    cF
    cfv
    #
    @62
    cG
    cfv
    #
    cr
    cr
    @13
    @44
    cr
    cr
    @1
    @17
    @49
    @49
    @34
    @16
    1red
    #
    wph
    @62
    @17
    wcel
    wa
    #
    @63
    wph
    @17
    cr
    @62
    cF
    fourierdlem61.f
    ffvelrnda
    recnd
    #
    wph
    @17
    cr
    @62
    cG
    wph
    @17
    cr
    cG
    wf
    @53
    @56
    wph
    @17
    @52
    cr
    cG
    @58
    feq2d
    mpbird
    #
    ffvelrnda
    #
    wph
    cr
    vs
    @1
    @12
    cmpt
    #
    cdv
    co
    vs
    @1
    cc0
    c1
    caddc
    co
    #
    cmpt
    vs
    @1
    c1
    cmpt
    #
    wph
    vs
    cA
    cc0
    @2
    c1
    cr
    cr
    cr
    @1
    @49
    wph
    cA
    cc
    wcel
    #
    @15
    @24
    adantr
    #
    @26
    wph
    vs
    cA
    cc0
    cr
    cioo
    crn
    ctg
    cfv
    #
    @38
    cr
    cr
    @1
    @49
    wph
    @73
    @21
    @24
    adantr
    wph
    @21
    wa
    #
    0red
    #
    wph
    vs
    cA
    cr
    @49
    @24
    dvmptc
    @1
    cr
    wss
    wph
    cc0
    @0
    ioossre
    a1i
    #
    @38
    @39
    tgioo2
    #
    @39
    @1
    @75
    wcel
    wph
    cc0
    @0
    iooretop
    a1i
    #
    dvmptres
    @16
    @2
    @22
    recnd
    #
    @65
    wph
    vs
    @2
    c1
    cr
    @75
    @38
    cr
    cr
    @1
    @49
    @21
    @2
    cc
    wcel
    wph
    @2
    recn
    adantl
    @76
    1red
    wph
    vs
    cr
    @49
    dvmptid
    @78
    @79
    @39
    @80
    dvmptres
    #
    dvmptadd
    vs
    @1
    @71
    c1
    0p1e1
    mpteq2i
    syl6eq
    wph
    cr
    vx
    @17
    @63
    cmpt
    #
    cdv
    co
    @51
    cG
    vx
    @17
    @64
    cmpt
    #
    wph
    @83
    cF
    cr
    cdv
    wph
    cF
    @83
    wph
    vx
    @17
    cr
    cF
    fourierdlem61.f
    feqmptd
    #
    eqcomd
    oveq2d
    @57
    wph
    vx
    @17
    cr
    cG
    @68
    feqmptd
    #
    3eqtrd
    @62
    @12
    cF
    fveq2
    #
    @62
    @12
    cG
    fveq2
    #
    dvmptco
    wph
    vs
    @1
    @61
    @44
    @16
    @44
    @16
    @44
    @59
    recnd
    #
    mulid1d
    mpteq2dva
    eqtrd
    wph
    cY
    cc
    wcel
    #
    @15
    wph
    cF
    cA
    climc
    co
    #
    cc
    cY
    cA
    cF
    limccl
    fourierdlem61.y
    sseldi
    #
    adantr
    #
    @29
    wph
    vs
    cY
    cc0
    cr
    @75
    @38
    cr
    cr
    @1
    @49
    wph
    @90
    @21
    @92
    adantr
    @77
    wph
    vs
    cY
    cr
    @49
    @92
    dvmptc
    @78
    @79
    @39
    @80
    dvmptres
    dvmptsub
    wph
    vs
    @1
    @48
    @44
    @16
    @44
    @89
    subid1d
    mpteq2dva
    eqtrd
    #
    dmeqd
    wph
    @44
    cr
    wcel
    #
    vs
    @1
    wral
    @46
    @1
    wceq
    wph
    @95
    vs
    @1
    @59
    ralrimiva
    vs
    @1
    @44
    cr
    dmmptg
    syl
    3eqtrd
    wph
    cr
    cD
    cdv
    co
    #
    cdm
    @72
    cdm
    #
    @1
    wph
    @96
    @72
    wph
    @96
    cr
    vs
    @1
    @2
    cmpt
    #
    cdv
    co
    @72
    wph
    cD
    @98
    cr
    cdv
    cD
    @98
    wceq
    wph
    fourierdlem61.d
    a1i
    #
    oveq2d
    @82
    eqtrd
    #
    dmeqd
    wph
    c1
    cr
    wcel
    #
    vs
    @1
    wral
    @97
    @1
    wceq
    wph
    @101
    vs
    @1
    @65
    ralrimiva
    vs
    @1
    c1
    cr
    dmmptg
    syl
    eqtrd
    wph
    cY
    cY
    cmin
    co
    @42
    cc0
    climc
    co
    #
    cc0
    cN
    cc0
    climc
    co
    #
    wph
    vs
    @1
    @13
    cY
    cc0
    cY
    @60
    vs
    @1
    cY
    cmpt
    #
    @42
    cY
    @60
    eqid
    @104
    eqid
    #
    @42
    eqid
    @50
    @93
    wph
    vs
    vx
    @1
    @17
    cA
    cY
    @12
    @63
    @13
    cc0
    wph
    @15
    @12
    @17
    wcel
    @12
    cA
    wne
    @34
    adantrr
    #
    @67
    wph
    cA
    @23
    @70
    cc0
    climc
    co
    @25
    wph
    vs
    @1
    cA
    @2
    cc0
    cA
    vs
    @1
    cA
    cmpt
    #
    @98
    @70
    cc0
    @107
    eqid
    #
    @98
    eqid
    #
    @70
    eqid
    @74
    @81
    wph
    vs
    @1
    cA
    cc0
    @107
    @108
    wph
    @1
    cr
    cc
    @78
    ax-resscn
    syl6ss
    #
    @24
    wph
    cc0
    @7
    recnd
    #
    constlimc
    wph
    vs
    @1
    @98
    cc0
    @110
    @109
    @111
    idlimc
    addlimc
    eqeltrd
    #
    wph
    cY
    @91
    @83
    cA
    climc
    co
    fourierdlem61.y
    wph
    cF
    @83
    cA
    climc
    @85
    oveq1d
    eleqtrd
    @87
    wph
    @15
    @12
    cA
    wceq
    #
    wa
    wa
    #
    @13
    cY
    wceq
    #
    @113
    wph
    @15
    @113
    @115
    wn
    #
    simplrr
    @114
    @113
    wn
    #
    @116
    wph
    @15
    @117
    @113
    @16
    @12
    cA
    @16
    cA
    @12
    @20
    @32
    gtned
    neneqd
    adantrr
    #
    adantr
    condan
    limcco
    wph
    vs
    @1
    cY
    cc0
    @104
    @105
    @110
    @92
    @111
    constlimc
    sublimc
    wph
    cY
    @92
    subidd
    @102
    @103
    wceq
    wph
    @42
    cN
    cc0
    climc
    cN
    @42
    fourierdlem61.n
    eqcomi
    oveq1i
    a1i
    3eltr3d
    wph
    vs
    @1
    cD
    cc0
    @110
    fourierdlem61.d
    @111
    idlimc
    wph
    @1
    cD
    crn
    #
    cc0
    cc0
    @1
    wcel
    wn
    wph
    cc0
    @0
    lbioo
    a1i
    wph
    @119
    cid
    @1
    cres
    #
    crn
    @1
    wph
    cD
    @120
    wph
    cD
    @98
    @120
    @99
    vs
    @1
    mptresid
    syl6eq
    rneqd
    @1
    rnresi
    syl6req
    neleqtrd
    wph
    c1
    csn
    #
    @96
    crn
    #
    cc0
    wph
    cc0
    @121
    wcel
    #
    cc0
    c1
    wceq
    #
    cc0
    c1
    0ne1
    neii
    wph
    cc0
    cr
    wcel
    @123
    @124
    wb
    @7
    cc0
    c1
    cr
    elsng
    syl
    mtbiri
    wph
    @122
    @72
    crn
    @121
    wph
    @96
    @72
    @100
    rneqd
    wph
    vs
    @1
    c1
    cr
    @72
    @72
    eqid
    #
    @65
    wph
    @1
    c0
    wne
    #
    @10
    @11
    wph
    @27
    @28
    @126
    @10
    wb
    @27
    wph
    0xr
    a1i
    @9
    cc0
    @0
    ioon0
    syl2anc
    mpbird
    rnmptc
    eqtr2d
    neleqtrd
    wph
    cE
    @45
    cc0
    climc
    co
    vs
    @1
    @2
    @41
    cfv
    #
    @2
    @96
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    climc
    co
    wph
    vs
    vx
    @1
    @17
    cA
    cE
    @12
    @64
    @44
    cc0
    @106
    @66
    @64
    @69
    recnd
    @112
    wph
    cE
    cG
    cA
    climc
    co
    @84
    cA
    climc
    co
    fourierdlem61.e
    wph
    cG
    @84
    cA
    climc
    @86
    oveq1d
    eleqtrd
    @88
    @114
    @44
    cE
    wceq
    #
    @113
    wph
    @15
    @113
    @131
    wn
    #
    simplrr
    @114
    @117
    @132
    @118
    adantr
    condan
    limcco
    wph
    @45
    @130
    cc0
    climc
    wph
    vs
    @1
    @44
    @129
    @16
    @44
    c1
    cdiv
    co
    @44
    @129
    @16
    @44
    @89
    div1d
    @16
    @44
    @127
    c1
    @128
    cdiv
    @16
    @127
    @2
    @45
    cfv
    #
    @44
    @16
    @2
    @41
    @45
    wph
    @41
    @45
    wceq
    @15
    wph
    @41
    @43
    @45
    @47
    @94
    syl5eq
    adantr
    fveq1d
    @16
    @15
    @95
    @133
    @44
    wceq
    @31
    @59
    vs
    @1
    @44
    cr
    @45
    @45
    eqid
    fvmpt2
    syl2anc
    eqtr2d
    @16
    @128
    @2
    @72
    cfv
    #
    c1
    wph
    @128
    @134
    wceq
    @15
    wph
    @2
    @96
    @72
    @100
    fveq1d
    adantr
    @16
    @15
    @101
    @134
    c1
    wceq
    @31
    @65
    vs
    @1
    c1
    cr
    @72
    @125
    fvmpt2
    syl2anc
    eqtr2d
    oveq12d
    eqtr3d
    mpteq2dva
    oveq1d
    eleqtrd
    lhop1
    wph
    @6
    cH
    cc0
    climc
    wph
    @6
    vs
    @1
    @14
    @2
    cdiv
    co
    #
    cmpt
    cH
    wph
    vs
    @1
    @5
    @135
    @16
    @3
    @14
    @4
    @2
    cdiv
    @16
    @15
    @14
    cr
    wcel
    @3
    @14
    wceq
    @31
    @40
    vs
    @1
    @14
    cr
    cN
    fourierdlem61.n
    fvmpt2
    syl2anc
    @16
    @15
    @15
    @4
    @2
    wceq
    @31
    @31
    vs
    @1
    @2
    @1
    cD
    fourierdlem61.d
    fvmpt2
    syl2anc
    oveq12d
    mpteq2dva
    fourierdlem61.h
    syl6eqr
    oveq1d
    eleqtrd
end
