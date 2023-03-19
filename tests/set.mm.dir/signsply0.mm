include "cneg.mm"
include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "simplr.mm"
include "simpr.mm"
include "cxr.mm"
include "rpxr.mm"
include "xrleid.mm"
include "syl.mm"
include "ad2antlr.mm"
include "id.mm"
include "breq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcdv.mm"
include "syl3c.mm"
include "caddc.mm"
include "cr.mm"
include "cply.mm"
include "ad2antrr.mm"
include "rpred.mm"
include "plyrecld.mm"
include "cn0.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "reexpcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "cz.mm"
include "nn0zd.mm"
include "expne0d.mm"
include "redivcld.mm"
include "wf.mm"
include "0re.mm"
include "coef2.mm"
include "mpan2.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "renegcld.mm"
include "absdifltd.mm"
include "simplbda.mm"
include "cc.mm"
include "recnd.mm"
include "negidd.mm"
include "adantr.mm"
include "breqtrd.mm"
include "wb.mm"
include "wn.mm"
include "rpexpcld.mm"
include "ge0divd.mm"
include "notbid.mm"
include "0red.mm"
include "ltnled.mm"
include "3bitr4d.mm"
include "mpbird.mm"
include "syldan.mm"
include "cioo.mm"
include "rpgt0d.mm"
include "cicc.mm"
include "wss.mm"
include "iccssre.mm"
include "sylancr.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ccncf.mm"
include "plycn.mm"
include "ad3antrrr.mm"
include "ad4antr.mm"
include "sselda.mm"
include "simplll.mm"
include "negelrp.mm"
include "biimpa.mm"
include "sylancl.mm"
include "0nn0.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "mul2lt0rlt0.mm"
include "syl6breq.mm"
include "coefv0.mm"
include "breqtrrd.mm"
include "jca.mm"
include "ivth2.mm"
include "cpnf.mm"
include "0le0.mm"
include "pnfge.mm"
include "0xr.mm"
include "pnfxr.mm"
include "ioossioo.mm"
include "mpanl12.mm"
include "ioorp.mm"
include "syl6sseq.mm"
include "ssrexv.mm"
include "3syl.mm"
include "mpd.mm"
include "c1.mm"
include "cico.mm"
include "cmpt.mm"
include "crli.mm"
include "cof.mm"
include "cvv.mm"
include "wfn.mm"
include "plyf.mm"
include "ffn.mm"
include "ovex.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "cnex.mm"
include "rpssre.mm"
include "sstri.mm"
include "ssexi.mm"
include "cin.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "eqidd.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "offval.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "signsplypnf.mm"
include "eqbrtrrd.mm"
include "expcld.mm"
include "divcld.mm"
include "ralrimiva.mm"
include "1red.mm"
include "rlim3.mm"
include "mpbid.mm"
include "0lt1.mm"
include "ax-mp.mm"
include "icossioo.mm"
include "mp4an.mm"
include "sseqtri.mm"
include "ralimi.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "r19.29a.mm"
include "subidd.mm"
include "simprbda.mm"
include "gt0divd.mm"
include "w3a.mm"
include "simpr1.mm"
include "3anassrs.mm"
include "mul2lt0rgt0.mm"
include "syl5eqbrr.mm"
include "eqbrtrd.mm"
include "ivth.mm"
include "wne.mm"
include "wo.mm"
include "c0p.mm"
include "dgreq0.mm"
include "necon3bid.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "rpneg.mm"
include "biimprd.mm"
include "orrd.mm"
include "mpjaodan.mm"

theorem signsply0
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vx: setvar x
  assume signsply0.d: |- D = ( deg ` F )
  assume signsply0.c: |- C = ( coeff ` F )
  assume signsply0.b: |- B = ( C ` D )
  assume signsply0.a: |- A = ( C ` 0 )
  assume signsply0.1: |- ( ph -> F e. ( Poly ` RR ) )
  assume signsply0.2: |- ( ph -> F =/= 0p )
  assume signsply0.3: |- ( ph -> ( A x. B ) < 0 )

  disjoint B z
  disjoint F z
  disjoint ph z
  disjoint d e
  disjoint d f
  disjoint d x
  disjoint B d
  disjoint e f
  disjoint e x
  disjoint B e
  disjoint f x
  disjoint B f
  disjoint B x
  disjoint d z
  disjoint x z
  disjoint C f
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D x
  disjoint F d
  disjoint e z
  disjoint F e
  disjoint f z
  disjoint F f
  disjoint F x
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint ph x
  assert |- ( ph -> E. z e. RR+ ( F ` z ) = 0 )

  proof
    wph
    cB
    cneg
    #
    crp
    wcel
    #
    vz
    cv
    cF
    cfv
    cc0
    wceq
    #
    vz
    crp
    wrex
    #
    cB
    crp
    wcel
    #
    wph
    @1
    wa
    #
    vd
    cv
    #
    vf
    cv
    #
    cle
    wbr
    #
    @7
    cF
    cfv
    #
    @7
    cD
    cexp
    co
    #
    cdiv
    co
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    clt
    wbr
    #
    wi
    #
    vf
    crp
    wral
    #
    @3
    vd
    crp
    @5
    @6
    crp
    wcel
    #
    wa
    #
    @16
    @6
    cF
    cfv
    #
    cc0
    clt
    wbr
    #
    @3
    @18
    @16
    @19
    @6
    cD
    cexp
    co
    #
    cdiv
    co
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    clt
    wbr
    #
    @20
    @18
    @16
    wa
    @17
    @16
    @6
    @6
    cle
    wbr
    #
    @25
    @5
    @17
    @16
    simplr
    @18
    @16
    simpr
    @17
    @26
    @5
    @16
    @17
    @6
    cxr
    wcel
    #
    @26
    @6
    rpxr
    #
    @6
    xrleid
    syl
    #
    ad2antlr
    @17
    @15
    @26
    @25
    wi
    vf
    @6
    crp
    @17
    id
    #
    @17
    @7
    @6
    wceq
    #
    wa
    #
    @8
    @26
    @14
    @25
    @32
    @7
    @6
    @6
    cle
    @17
    @31
    simpr
    #
    breq2d
    #
    @32
    @13
    @24
    @0
    clt
    @32
    @12
    @23
    cabs
    @32
    @11
    @22
    cB
    cmin
    @32
    @9
    @19
    @10
    @21
    cdiv
    @32
    @7
    @6
    cF
    @33
    fveq2d
    @32
    @7
    @6
    cD
    cexp
    @33
    oveq1d
    oveq12d
    oveq1d
    fveq2d
    #
    breq1d
    imbi12d
    rspcdv
    syl3c
    @18
    @25
    wa
    #
    @20
    @22
    cc0
    clt
    wbr
    #
    @36
    @22
    cB
    @0
    caddc
    co
    #
    cc0
    clt
    @18
    @25
    cB
    @0
    cmin
    co
    @22
    clt
    wbr
    @22
    @38
    clt
    wbr
    @18
    @22
    cB
    @0
    @18
    @19
    @21
    @18
    cF
    @6
    wph
    cF
    cr
    cply
    cfv
    wcel
    #
    @1
    @17
    signsply0.1
    ad2antrr
    @18
    @6
    @5
    @17
    simpr
    #
    rpred
    #
    plyrecld
    #
    @18
    @6
    cD
    @41
    wph
    cD
    cn0
    wcel
    #
    @1
    @17
    wph
    cD
    cF
    cdgr
    cfv
    #
    cn0
    signsply0.d
    wph
    @39
    @44
    cn0
    wcel
    signsply0.1
    cr
    cF
    dgrcl
    syl
    syl5eqel
    #
    ad2antrr
    reexpcld
    @18
    @6
    cD
    @18
    @6
    @40
    rpcnd
    @18
    @6
    @40
    rpne0d
    wph
    cD
    cz
    wcel
    #
    @1
    @17
    wph
    cD
    @45
    nn0zd
    #
    ad2antrr
    #
    expne0d
    redivcld
    #
    wph
    cB
    cr
    wcel
    #
    @1
    @17
    wph
    @39
    @43
    @50
    signsply0.1
    @45
    @39
    @43
    wa
    cB
    cD
    cC
    cfv
    #
    cr
    signsply0.b
    @39
    cn0
    cr
    cD
    cC
    @39
    cc0
    cr
    wcel
    #
    cn0
    cr
    cC
    wf
    #
    0re
    cC
    cr
    cF
    signsply0.c
    coef2
    #
    mpan2
    ffvelrnda
    syl5eqel
    syl2anc
    #
    ad2antrr
    #
    @18
    cB
    @56
    renegcld
    absdifltd
    simplbda
    @18
    @38
    cc0
    wceq
    @25
    @18
    cB
    wph
    cB
    cc
    wcel
    #
    @1
    @17
    wph
    cB
    @55
    recnd
    #
    ad2antrr
    negidd
    adantr
    breqtrd
    @18
    @20
    @37
    wb
    @25
    @18
    cc0
    @19
    cle
    wbr
    #
    wn
    cc0
    @22
    cle
    wbr
    #
    wn
    @20
    @37
    @18
    @59
    @60
    @18
    @19
    @21
    @42
    @18
    @6
    cD
    @40
    @48
    rpexpcld
    ge0divd
    notbid
    @18
    @19
    cc0
    @42
    @18
    0red
    #
    ltnled
    @18
    @22
    cc0
    @49
    @61
    ltnled
    3bitr4d
    adantr
    mpbird
    syldan
    @18
    @20
    wa
    #
    @2
    vz
    cc0
    @6
    cioo
    co
    #
    wrex
    #
    @3
    @62
    vx
    cc0
    @6
    cc
    cc0
    cF
    vz
    @62
    0red
    #
    @62
    @6
    @5
    @17
    @20
    simplr
    #
    rpred
    #
    @65
    @62
    @6
    @66
    rpgt0d
    @62
    cc0
    @6
    cicc
    co
    #
    cr
    cc
    @62
    @52
    @6
    cr
    wcel
    #
    @68
    cr
    wss
    #
    0re
    @67
    cc0
    @6
    iccssre
    #
    sylancr
    #
    ax-resscn
    syl6ss
    wph
    cF
    cc
    cc
    ccncf
    co
    wcel
    #
    @1
    @17
    @20
    wph
    @39
    @73
    signsply0.1
    cr
    cF
    plycn
    syl
    #
    ad3antrrr
    @62
    vx
    cv
    #
    @68
    wcel
    #
    wa
    cF
    @75
    wph
    @39
    @1
    @17
    @20
    @76
    signsply0.1
    ad4antr
    @62
    @68
    cr
    @75
    @72
    sselda
    plyrecld
    @62
    @20
    cc0
    cc0
    cF
    cfv
    #
    clt
    wbr
    @18
    @20
    simpr
    @62
    cc0
    cc0
    cC
    cfv
    #
    @77
    clt
    @62
    wph
    cB
    cc0
    clt
    wbr
    #
    cc0
    @78
    clt
    wbr
    wph
    @1
    @17
    @20
    simplll
    #
    @62
    @50
    @1
    @79
    @62
    wph
    @50
    @80
    @55
    syl
    @5
    @1
    @17
    @20
    wph
    @1
    simpr
    #
    ad2antrr
    @50
    @1
    @79
    cB
    negelrp
    biimpa
    syl2anc
    wph
    @79
    wa
    cc0
    cA
    @78
    clt
    wph
    cA
    cB
    wph
    cA
    @78
    cr
    signsply0.a
    wph
    cn0
    cr
    cc0
    cC
    wph
    @39
    @52
    @53
    signsply0.1
    0re
    @54
    sylancl
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    ffvelrnd
    syl5eqel
    #
    @55
    signsply0.3
    mul2lt0rlt0
    signsply0.a
    syl6breq
    syl2anc
    wph
    @77
    @78
    wceq
    #
    @1
    @17
    @20
    wph
    @39
    @83
    signsply0.1
    cC
    cr
    cF
    signsply0.c
    coefv0
    syl
    #
    ad3antrrr
    breqtrrd
    jca
    ivth2
    @62
    @17
    @63
    crp
    wss
    #
    @64
    @3
    wi
    #
    @66
    @17
    @63
    cc0
    cpnf
    cioo
    co
    #
    crp
    @17
    cc0
    cc0
    cle
    wbr
    #
    @6
    cpnf
    cle
    wbr
    #
    @63
    @87
    wss
    #
    0le0
    @17
    @27
    @89
    @28
    @6
    pnfge
    syl
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @88
    @89
    wa
    @90
    0xr
    pnfxr
    cc0
    cpnf
    cc0
    @6
    ioossioo
    mpanl12
    sylancr
    ioorp
    syl6sseq
    #
    @2
    vz
    @63
    crp
    ssrexv
    #
    3syl
    mpd
    syldan
    @5
    @8
    @13
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vf
    crp
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    #
    @16
    vd
    crp
    wrex
    #
    wph
    @100
    @1
    wph
    @98
    vd
    c1
    cpnf
    cico
    co
    #
    wrex
    #
    ve
    crp
    wral
    #
    @100
    wph
    vf
    crp
    @11
    cmpt
    #
    cB
    crli
    wbr
    @104
    wph
    cF
    vx
    crp
    @75
    cD
    cexp
    co
    #
    cmpt
    #
    cdiv
    cof
    co
    #
    @105
    cB
    crli
    wph
    vf
    cc
    crp
    @9
    @10
    cdiv
    crp
    cF
    @107
    cvv
    cvv
    wph
    cc
    cc
    cF
    wf
    #
    cF
    cc
    wfn
    wph
    @39
    @109
    signsply0.1
    cr
    cF
    plyf
    syl
    #
    cc
    cc
    cF
    ffn
    syl
    @106
    cvv
    wcel
    #
    vx
    crp
    wral
    @107
    crp
    wfn
    wph
    @111
    vx
    crp
    @75
    cD
    cexp
    ovex
    rgenw
    vx
    crp
    @106
    @107
    cvv
    @107
    eqid
    fnmpt
    mp1i
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    crp
    cvv
    wcel
    wph
    crp
    cc
    cnex
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    #
    ssexi
    a1i
    crp
    cc
    wss
    cc
    crp
    cin
    crp
    wceq
    @112
    crp
    cc
    sseqin2
    mpbi
    wph
    @7
    cc
    wcel
    wa
    @9
    eqidd
    wph
    @7
    crp
    wcel
    #
    wa
    #
    vx
    @7
    @106
    @10
    crp
    @107
    cvv
    @114
    @107
    eqidd
    @114
    @75
    @7
    wceq
    #
    wa
    @75
    @7
    cD
    cexp
    @114
    @115
    simpr
    oveq1d
    wph
    @113
    simpr
    #
    @114
    @7
    cD
    cexp
    ovexd
    fvmptd
    offval
    wph
    @39
    @108
    cB
    crli
    wbr
    signsply0.1
    vf
    cB
    cC
    cD
    cF
    @107
    signsply0.d
    signsply0.c
    signsply0.b
    vx
    vf
    crp
    @106
    @10
    @75
    @7
    cD
    cexp
    oveq1
    cbvmptv
    signsplypnf
    syl
    eqbrtrrd
    wph
    ve
    vd
    vf
    crp
    @11
    cB
    c1
    wph
    @11
    cc
    wcel
    vf
    crp
    @114
    @9
    @10
    @114
    cc
    cc
    @7
    cF
    wph
    @109
    @113
    @110
    adantr
    @114
    @7
    @116
    rpcnd
    #
    ffvelrnd
    @114
    @7
    cD
    @117
    wph
    @43
    @113
    @45
    adantr
    expcld
    @114
    @7
    cD
    @117
    @114
    @7
    @116
    rpne0d
    wph
    @46
    @113
    @47
    adantr
    expne0d
    divcld
    ralrimiva
    crp
    cr
    wss
    #
    wph
    rpssre
    a1i
    @58
    wph
    1red
    rlim3
    mpbid
    @103
    @99
    ve
    crp
    @102
    crp
    wss
    @103
    @99
    wi
    @102
    @87
    crp
    @91
    @92
    cc0
    c1
    clt
    wbr
    cpnf
    cpnf
    cle
    wbr
    #
    @102
    @87
    wss
    0xr
    pnfxr
    0lt1
    @92
    @119
    pnfxr
    cpnf
    pnfge
    ax-mp
    cc0
    cpnf
    c1
    cpnf
    icossioo
    mp4an
    ioorp
    sseqtri
    @98
    vd
    @102
    crp
    ssrexv
    ax-mp
    ralimi
    syl
    #
    adantr
    @5
    @99
    @101
    ve
    @0
    crp
    @81
    @5
    @95
    @0
    wceq
    #
    wa
    #
    @97
    @15
    vd
    vf
    crp
    crp
    @122
    @96
    @14
    @8
    @122
    @95
    @0
    @13
    clt
    @5
    @121
    simpr
    breq2d
    imbi2d
    rexralbidv
    rspcdv
    mpd
    r19.29a
    wph
    @4
    wa
    #
    @8
    @13
    cB
    clt
    wbr
    #
    wi
    #
    vf
    crp
    wral
    #
    @3
    vd
    crp
    @123
    @17
    wa
    #
    @126
    cc0
    @19
    clt
    wbr
    #
    @3
    @127
    @126
    @24
    cB
    clt
    wbr
    #
    @128
    @127
    @126
    wa
    @17
    @126
    @26
    @129
    @123
    @17
    @126
    simplr
    @127
    @126
    simpr
    @17
    @26
    @123
    @126
    @29
    ad2antlr
    @17
    @125
    @26
    @129
    wi
    vf
    @6
    crp
    @30
    @32
    @8
    @26
    @124
    @129
    @34
    @32
    @13
    @24
    cB
    clt
    @35
    breq1d
    imbi12d
    rspcdv
    syl3c
    @127
    @129
    wa
    #
    @128
    cc0
    @22
    clt
    wbr
    #
    @130
    cB
    cB
    cmin
    co
    #
    cc0
    @22
    clt
    @127
    @132
    cc0
    wceq
    @129
    @127
    cB
    wph
    @57
    @4
    @17
    @58
    ad2antrr
    subidd
    adantr
    @127
    @129
    @132
    @22
    clt
    wbr
    @22
    cB
    cB
    caddc
    co
    clt
    wbr
    @127
    @22
    cB
    cB
    @127
    @19
    @21
    @127
    cF
    @6
    wph
    @39
    @4
    @17
    signsply0.1
    ad2antrr
    @123
    crp
    cr
    @6
    @118
    @123
    rpssre
    a1i
    sselda
    #
    plyrecld
    #
    @127
    @6
    cD
    @133
    wph
    @43
    @4
    @17
    @45
    ad2antrr
    reexpcld
    @127
    @6
    cD
    @127
    @6
    @133
    recnd
    @127
    @6
    @123
    @17
    simpr
    #
    rpne0d
    wph
    @46
    @4
    @17
    @47
    ad2antrr
    #
    expne0d
    redivcld
    wph
    @50
    @4
    @17
    @55
    ad2antrr
    #
    @137
    absdifltd
    simprbda
    eqbrtrrd
    @127
    @128
    @131
    wb
    @129
    @127
    @19
    @21
    @134
    @127
    @6
    cD
    @135
    @136
    rpexpcld
    gt0divd
    adantr
    mpbird
    syldan
    @127
    @128
    wa
    #
    @64
    @3
    @138
    vx
    cc0
    @6
    cc
    cc0
    cF
    vz
    @138
    0red
    #
    @138
    @6
    @123
    @17
    @128
    simplr
    #
    rpred
    #
    @139
    @138
    @6
    @140
    rpgt0d
    @138
    @68
    cr
    cc
    @138
    @52
    @69
    @70
    0re
    @141
    @71
    sylancr
    #
    ax-resscn
    syl6ss
    wph
    @73
    @4
    @17
    @128
    @74
    ad3antrrr
    @138
    @76
    wa
    cF
    @75
    wph
    @39
    @4
    @17
    @128
    @76
    signsply0.1
    ad4antr
    @138
    @68
    cr
    @75
    @142
    sselda
    plyrecld
    @138
    @77
    cc0
    clt
    wbr
    @128
    @138
    @77
    @78
    cc0
    clt
    wph
    @83
    @4
    @17
    @128
    @84
    ad3antrrr
    @138
    @78
    cA
    cc0
    clt
    signsply0.a
    @138
    wph
    cc0
    cB
    clt
    wbr
    #
    cA
    cc0
    clt
    wbr
    wph
    @4
    @17
    @128
    simplll
    wph
    @4
    @17
    @128
    @143
    wph
    @4
    @17
    @128
    w3a
    wa
    cB
    wph
    @4
    @17
    @128
    simpr1
    rpgt0d
    3anassrs
    wph
    cA
    cB
    @82
    @55
    signsply0.3
    mul2lt0rgt0
    syl2anc
    syl5eqbrr
    eqbrtrd
    @127
    @128
    simpr
    jca
    ivth
    @138
    @17
    @85
    @86
    @140
    @93
    @94
    3syl
    mpd
    syldan
    @123
    @100
    @126
    vd
    crp
    wrex
    #
    wph
    @100
    @4
    @120
    adantr
    @123
    @99
    @144
    ve
    cB
    crp
    wph
    @4
    simpr
    @123
    @95
    cB
    wceq
    #
    wa
    #
    @97
    @125
    vd
    vf
    crp
    crp
    @146
    @96
    @124
    @8
    @146
    @95
    cB
    @13
    clt
    @123
    @145
    simpr
    breq2d
    imbi2d
    rexralbidv
    rspcdv
    mpd
    r19.29a
    wph
    @50
    cB
    cc0
    wne
    #
    @1
    @4
    wo
    @55
    wph
    @51
    cc0
    wne
    #
    @147
    wph
    cF
    c0p
    wne
    @148
    signsply0.2
    wph
    cF
    c0p
    @51
    cc0
    wph
    @39
    cF
    c0p
    wceq
    @51
    cc0
    wceq
    wb
    signsply0.1
    cC
    cr
    cF
    cD
    signsply0.d
    signsply0.c
    dgreq0
    syl
    necon3bid
    mpbid
    cB
    @51
    cc0
    signsply0.b
    neeq1i
    sylibr
    @50
    @147
    wa
    #
    @1
    @4
    @149
    @4
    @1
    wn
    cB
    rpneg
    biimprd
    orrd
    syl2anc
    mpjaodan
end
