include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cioo.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "resubcld.mm"
include "rexrd.mm"
include "0red.mm"
include "clt.mm"
include "wbr.mm"
include "sublt0d.mm"
include "mpbird.mm"
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
include "pncan3d.mm"
include "eqcomd.mm"
include "0xr.mm"
include "a1i.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "iooltub.mm"
include "addid1d.mm"
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
include "lptioo2cn.mm"
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
include "eqeltrrd.mm"
include "oveq1d.mm"
include "wn.mm"
include "simplrr.mm"
include "ltned.mm"
include "neneqd.mm"
include "condan.mm"
include "limcco.mm"
include "sublimc.mm"
include "subidd.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3eltr3d.mm"
include "ubioo.mm"
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
include "lhop2.mm"
include "syl6eqr.mm"

theorem fourierdlem60
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
  assume fourierdlem60.a: |- ( ph -> A e. RR )
  assume fourierdlem60.b: |- ( ph -> B e. RR )
  assume fourierdlem60.altb: |- ( ph -> A < B )
  assume fourierdlem60.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume fourierdlem60.y: |- ( ph -> Y e. ( F limCC B ) )
  assume fourierdlem60.g: |- G = ( RR _D F )
  assume fourierdlem60.domg: |- ( ph -> dom G = ( A (,) B ) )
  assume fourierdlem60.e: |- ( ph -> E e. ( G limCC B ) )
  assume fourierdlem60.h: |- H = ( s e. ( ( A - B ) (,) 0 ) |-> ( ( ( F ` ( B + s ) ) - Y ) / s ) )
  assume fourierdlem60.n: |- N = ( s e. ( ( A - B ) (,) 0 ) |-> ( ( F ` ( B + s ) ) - Y ) )
  assume fourierdlem60.d: |- D = ( s e. ( ( A - B ) (,) 0 ) |-> s )

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
    cA
    cB
    cmin
    co
    #
    cc0
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
    @0
    cc0
    cE
    cN
    cD
    wph
    @0
    wph
    cA
    cB
    fourierdlem60.a
    fourierdlem60.b
    resubcld
    #
    rexrd
    #
    wph
    0red
    #
    wph
    @0
    cc0
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    fourierdlem60.altb
    wph
    cA
    cB
    fourierdlem60.a
    fourierdlem60.b
    sublt0d
    mpbird
    #
    wph
    vs
    @1
    cB
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
    fourierdlem60.f
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
    fourierdlem60.a
    rexrd
    #
    adantr
    wph
    cB
    cxr
    wcel
    @15
    wph
    cB
    fourierdlem60.b
    rexrd
    adantr
    @16
    cB
    @2
    wph
    cB
    cr
    wcel
    @15
    fourierdlem60.b
    adantr
    #
    @15
    @2
    cr
    wcel
    #
    wph
    @2
    @0
    cc0
    elioore
    adantl
    #
    readdcld
    #
    @16
    cA
    cB
    @0
    caddc
    co
    #
    @12
    clt
    wph
    cA
    @24
    wceq
    @15
    wph
    @24
    cA
    wph
    cB
    cA
    wph
    cB
    fourierdlem60.b
    recnd
    #
    wph
    cA
    fourierdlem60.a
    recnd
    pncan3d
    eqcomd
    adantr
    @16
    @0
    @2
    cB
    wph
    @0
    cr
    wcel
    @15
    @7
    adantr
    @22
    @20
    @16
    @0
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    #
    @15
    @0
    @2
    clt
    wbr
    wph
    @26
    @15
    @8
    adantr
    #
    @27
    @16
    0xr
    a1i
    #
    wph
    @15
    simpr
    #
    @0
    cc0
    @2
    ioogtlb
    syl3anc
    ltadd2dd
    eqbrtrd
    @16
    @12
    cB
    cc0
    caddc
    co
    #
    cB
    clt
    @16
    @2
    cc0
    cB
    @22
    @16
    0red
    #
    @20
    @16
    @26
    @27
    @15
    @2
    cc0
    clt
    wbr
    @28
    @29
    @30
    @0
    cc0
    @2
    iooltub
    syl3anc
    ltadd2dd
    wph
    @31
    cB
    wceq
    @15
    wph
    cB
    @25
    addid1d
    #
    adantr
    breqtrd
    #
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
    cB
    cF
    cY
    fourierdlem60.f
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
    @39
    eqid
    #
    @19
    fourierdlem60.b
    fourierdlem60.altb
    lptioo2cn
    fourierdlem60.y
    limcrecl
    adantr
    resubcld
    #
    fourierdlem60.n
    fmptd
    wph
    vs
    @1
    @2
    cr
    cD
    @22
    fourierdlem60.d
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
    @42
    @44
    @42
    @44
    wceq
    wph
    cN
    @43
    cr
    cdv
    fourierdlem60.n
    oveq2i
    #
    a1i
    dmeqd
    wph
    @44
    @46
    wph
    @44
    vs
    @1
    @45
    cc0
    cmin
    co
    #
    cmpt
    @46
    wph
    vs
    @13
    @45
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
    @36
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
    @53
    cr
    cG
    wf
    #
    @15
    wph
    @54
    @53
    cr
    @52
    wf
    #
    wph
    @18
    @37
    @55
    fourierdlem60.f
    @38
    @17
    cF
    dvfre
    syl2anc
    wph
    @53
    cr
    cG
    @52
    cG
    @52
    wceq
    wph
    fourierdlem60.g
    a1i
    #
    feq1d
    mpbird
    #
    adantr
    @16
    @12
    @17
    @53
    @35
    wph
    @17
    @53
    wceq
    @15
    wph
    @53
    cG
    cdm
    @17
    wph
    @52
    cG
    wph
    cG
    @52
    @56
    eqcomd
    #
    dmeqd
    fourierdlem60.domg
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
    @45
    c1
    cmul
    co
    #
    cmpt
    @46
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
    @63
    cG
    cfv
    #
    cr
    cr
    @13
    @45
    cr
    cr
    @1
    @17
    @50
    @50
    @35
    @16
    1red
    #
    wph
    @63
    @17
    wcel
    wa
    #
    @64
    wph
    @17
    cr
    @63
    cF
    fourierdlem60.f
    ffvelrnda
    recnd
    #
    wph
    @17
    cr
    @63
    cG
    wph
    @17
    cr
    cG
    wf
    @54
    @57
    wph
    @17
    @53
    cr
    cG
    @59
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
    cB
    cc0
    @2
    c1
    cr
    cr
    cr
    @1
    @50
    wph
    cB
    cc
    wcel
    #
    @15
    @25
    adantr
    #
    @32
    wph
    vs
    cB
    cc0
    cr
    cioo
    crn
    ctg
    cfv
    #
    @39
    cr
    cr
    @1
    @50
    wph
    @74
    @21
    @25
    adantr
    wph
    @21
    wa
    #
    0red
    #
    wph
    vs
    cB
    cr
    @50
    @25
    dvmptc
    @1
    cr
    wss
    wph
    @0
    cc0
    ioossre
    a1i
    #
    @39
    @40
    tgioo2
    #
    @40
    @1
    @76
    wcel
    wph
    @0
    cc0
    iooretop
    a1i
    #
    dvmptres
    @16
    @2
    @22
    recnd
    #
    @66
    wph
    vs
    @2
    c1
    cr
    @76
    @39
    cr
    cr
    @1
    @50
    @21
    @2
    cc
    wcel
    wph
    @2
    recn
    adantl
    @77
    1red
    wph
    vs
    cr
    @50
    dvmptid
    @79
    @80
    @40
    @81
    dvmptres
    #
    dvmptadd
    vs
    @1
    @72
    c1
    0p1e1
    mpteq2i
    syl6eq
    wph
    cr
    vx
    @17
    @64
    cmpt
    #
    cdv
    co
    @52
    cG
    vx
    @17
    @65
    cmpt
    #
    wph
    @84
    cF
    cr
    cdv
    wph
    cF
    @84
    wph
    vx
    @17
    cr
    cF
    fourierdlem60.f
    feqmptd
    #
    eqcomd
    oveq2d
    @58
    wph
    vx
    @17
    cr
    cG
    @69
    feqmptd
    #
    3eqtrd
    @63
    @12
    cF
    fveq2
    #
    @63
    @12
    cG
    fveq2
    #
    dvmptco
    wph
    vs
    @1
    @62
    @45
    @16
    @45
    @16
    @45
    @60
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
    cB
    climc
    co
    #
    cc
    cY
    cB
    cF
    limccl
    fourierdlem60.y
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
    @76
    @39
    cr
    cr
    @1
    @50
    wph
    @91
    @21
    @93
    adantr
    @78
    wph
    vs
    cY
    cr
    @50
    @93
    dvmptc
    @79
    @80
    @40
    @81
    dvmptres
    dvmptsub
    wph
    vs
    @1
    @49
    @45
    @16
    @45
    @90
    subid1d
    mpteq2dva
    eqtrd
    #
    dmeqd
    wph
    @45
    cr
    wcel
    #
    vs
    @1
    wral
    @47
    @1
    wceq
    wph
    @96
    vs
    @1
    @60
    ralrimiva
    vs
    @1
    @45
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
    @73
    cdm
    #
    @1
    wph
    @97
    @73
    wph
    @97
    cr
    vs
    @1
    @2
    cmpt
    #
    cdv
    co
    @73
    wph
    cD
    @99
    cr
    cdv
    cD
    @99
    wceq
    wph
    fourierdlem60.d
    a1i
    #
    oveq2d
    @83
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
    @98
    @1
    wceq
    wph
    @102
    vs
    @1
    @66
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
    @43
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
    @61
    vs
    @1
    cY
    cmpt
    #
    @43
    cY
    @61
    eqid
    @105
    eqid
    #
    @43
    eqid
    @51
    @94
    wph
    vs
    vx
    @1
    @17
    cB
    cY
    @12
    @64
    @13
    cc0
    wph
    @15
    @12
    @17
    wcel
    @12
    cB
    wne
    @35
    adantrr
    #
    @68
    wph
    @31
    cB
    @71
    cc0
    climc
    co
    @33
    wph
    vs
    @1
    cB
    @2
    cc0
    cB
    vs
    @1
    cB
    cmpt
    #
    @99
    @71
    cc0
    @108
    eqid
    #
    @99
    eqid
    #
    @71
    eqid
    @75
    @82
    wph
    vs
    @1
    cB
    cc0
    @108
    @109
    wph
    @1
    cr
    cc
    @79
    ax-resscn
    syl6ss
    #
    @25
    wph
    cc0
    @9
    recnd
    #
    constlimc
    wph
    vs
    @1
    @99
    cc0
    @111
    @110
    @112
    idlimc
    addlimc
    eqeltrrd
    #
    wph
    cY
    @92
    @84
    cB
    climc
    co
    fourierdlem60.y
    wph
    cF
    @84
    cB
    climc
    @86
    oveq1d
    eleqtrd
    @88
    wph
    @15
    @12
    cB
    wceq
    #
    wa
    wa
    #
    @13
    cY
    wceq
    #
    @114
    wph
    @15
    @114
    @116
    wn
    #
    simplrr
    @115
    @114
    wn
    #
    @117
    wph
    @15
    @118
    @114
    @16
    @12
    cB
    @16
    @12
    cB
    @23
    @34
    ltned
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
    @105
    @106
    @111
    @93
    @112
    constlimc
    sublimc
    wph
    cY
    @93
    subidd
    @103
    @104
    wceq
    wph
    @43
    cN
    cc0
    climc
    cN
    @43
    fourierdlem60.n
    eqcomi
    oveq1i
    a1i
    3eltr3d
    wph
    vs
    @1
    cD
    cc0
    @111
    fourierdlem60.d
    @112
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
    @0
    cc0
    ubioo
    a1i
    wph
    @120
    cid
    @1
    cres
    #
    crn
    @1
    wph
    cD
    @121
    wph
    cD
    @99
    @121
    @100
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
    @97
    crn
    #
    cc0
    wph
    cc0
    @122
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
    @124
    @125
    wb
    @9
    cc0
    c1
    cr
    elsng
    syl
    mtbiri
    wph
    @123
    @73
    crn
    @122
    wph
    @97
    @73
    @101
    rneqd
    wph
    vs
    @1
    c1
    cr
    @73
    @73
    eqid
    #
    @66
    wph
    @1
    c0
    wne
    #
    @10
    @11
    wph
    @26
    @27
    @127
    @10
    wb
    @8
    @27
    wph
    0xr
    a1i
    @0
    cc0
    ioon0
    syl2anc
    mpbird
    rnmptc
    eqtr2d
    neleqtrd
    wph
    cE
    @46
    cc0
    climc
    co
    vs
    @1
    @2
    @42
    cfv
    #
    @2
    @97
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
    cB
    cE
    @12
    @65
    @45
    cc0
    @107
    @67
    @65
    @70
    recnd
    @113
    wph
    cE
    cG
    cB
    climc
    co
    @85
    cB
    climc
    co
    fourierdlem60.e
    wph
    cG
    @85
    cB
    climc
    @87
    oveq1d
    eleqtrd
    @89
    @115
    @45
    cE
    wceq
    #
    @114
    wph
    @15
    @114
    @132
    wn
    #
    simplrr
    @115
    @118
    @133
    @119
    adantr
    condan
    limcco
    wph
    @46
    @131
    cc0
    climc
    wph
    vs
    @1
    @45
    @130
    @16
    @45
    c1
    cdiv
    co
    @45
    @130
    @16
    @45
    @90
    div1d
    @16
    @45
    @128
    c1
    @129
    cdiv
    @16
    @128
    @2
    @46
    cfv
    #
    @45
    @16
    @2
    @42
    @46
    wph
    @42
    @46
    wceq
    @15
    wph
    @42
    @44
    @46
    @48
    @95
    syl5eq
    adantr
    fveq1d
    @16
    @15
    @96
    @134
    @45
    wceq
    @30
    @60
    vs
    @1
    @45
    cr
    @46
    @46
    eqid
    fvmpt2
    syl2anc
    eqtr2d
    @16
    @129
    @2
    @73
    cfv
    #
    c1
    wph
    @129
    @135
    wceq
    @15
    wph
    @2
    @97
    @73
    @101
    fveq1d
    adantr
    @16
    @15
    @102
    @135
    c1
    wceq
    @30
    @66
    vs
    @1
    c1
    cr
    @73
    @126
    fvmpt2
    syl2anc
    eqtr2d
    oveq12d
    eqtr3d
    mpteq2dva
    oveq1d
    eleqtrd
    lhop2
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
    @136
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
    @30
    @41
    vs
    @1
    @14
    cr
    cN
    fourierdlem60.n
    fvmpt2
    syl2anc
    @16
    @15
    @15
    @4
    @2
    wceq
    @30
    @30
    vs
    @1
    @2
    @1
    cD
    fourierdlem60.d
    fvmpt2
    syl2anc
    oveq12d
    mpteq2dva
    fourierdlem60.h
    syl6eqr
    oveq1d
    eleqtrd
end
