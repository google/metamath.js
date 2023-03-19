include "cv.mm"
include "crrx.mm"
include "cfv.mm"
include "cds.mm"
include "cbl.mm"
include "co.mm"
include "wcel.mm"
include "cico.mm"
include "cixp.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cr.mm"
include "cmap.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cfn.mm"
include "eqid.mm"
include "rrxdsfi.mm"
include "syl.mm"
include "adantr.mm"
include "fveq1.mm"
include "adantl.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "sumeq2ad.mm"
include "fveq2d.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "hoissrrn2.mm"
include "simpr.mm"
include "sseldd.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "nfcv.mm"
include "nfixp1.mm"
include "nfel.mm"
include "nfan.mm"
include "simpl.mm"
include "wf.mm"
include "elmapi.mm"
include "sylan.mm"
include "cxr.mm"
include "icossre.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "fvixp2.mm"
include "adantll.mm"
include "resubcld.mm"
include "cn0.mm"
include "2nn0.mm"
include "a1i.mm"
include "reexpcld.mm"
include "fsumreclf.mm"
include "cc0.mm"
include "cle.mm"
include "fveq2.mm"
include "cbvixpv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simpll.mm"
include "biimpri.mm"
include "ad2antlr.mm"
include "syl21anc.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "resqrtcld.mm"
include "eqeltrd.mm"
include "resqcld.mm"
include "fsumrecl.mm"
include "rpred.mm"
include "c0.mm"
include "wne.mm"
include "cabs.mm"
include "chash.mm"
include "cmul.mm"
include "cdiv.mm"
include "cioo.mm"
include "crp.mm"
include "2rp.mm"
include "cn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnred.mm"
include "nngt0d.mm"
include "elrpd.mm"
include "rpsqrtcld.mm"
include "rpmulcld.mm"
include "rpdivcld.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "ltled.mm"
include "caddc.mm"
include "readdcld.mm"
include "ioogtlb.mm"
include "elicod.mm"
include "icodiamlt.mm"
include "syl22anc.mm"
include "0red.mm"
include "lelttrd.mm"
include "posdifd.mm"
include "mpbid.mm"
include "absidd.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "abslt2sqd.mm"
include "fsumlt.mm"
include "sqrtltd.mm"
include "eqbrtrd.mm"
include "rerpdivcld.mm"
include "jca.mm"
include "lt2sub.mm"
include "sylc.mm"
include "recnd.mm"
include "pnncand.mm"
include "rpcnd.mm"
include "2cnd.mm"
include "rpne0d.mm"
include "divdiv3d.mm"
include "divcld.mm"
include "2halvesd.mm"
include "eqtrd.mm"
include "rpgt0d.mm"
include "divgt0d.mm"
include "lt2sq.mm"
include "cc.mm"
include "fsumconst.mm"
include "sqdiv.mm"
include "sqrtth.mm"
include "oveq2d.mm"
include "sqcld.mm"
include "gtned.mm"
include "divcan2d.mm"
include "3eqtrd.mm"
include "sqrtsq.mm"
include "eqidd.mm"
include "lttrd.mm"
include "cxmt.mm"
include "cme.mm"
include "rrxmetfi.mm"
include "metxmet.mm"
include "3syl.mm"
include "syl6eleq.mm"
include "elbl2.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem hoiqssbllem2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cE: class E
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume hoiqssbllem2.i: |- F/ i ph
  assume hoiqssbllem2.x: |- ( ph -> X e. Fin )
  assume hoiqssbllem2.n: |- ( ph -> X =/= (/) )
  assume hoiqssbllem2.y: |- ( ph -> Y e. ( RR ^m X ) )
  assume hoiqssbllem2.c: |- ( ph -> C : X --> RR )
  assume hoiqssbllem2.d: |- ( ph -> D : X --> RR )
  assume hoiqssbllem2.e: |- ( ph -> E e. RR+ )
  assume hoiqssbllem2.l: |- ( ( ph /\ i e. X ) -> ( C ` i ) e. ( ( ( Y ` i ) - ( E / ( 2 x. ( sqrt ` ( # ` X ) ) ) ) ) (,) ( Y ` i ) ) )
  assume hoiqssbllem2.r: |- ( ( ph /\ i e. X ) -> ( D ` i ) e. ( ( Y ` i ) (,) ( ( Y ` i ) + ( E / ( 2 x. ( sqrt ` ( # ` X ) ) ) ) ) ) )

  disjoint C i
  disjoint D i
  disjoint E i
  disjoint X i
  disjoint Y i
  disjoint i ph
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint g h
  disjoint g i
  disjoint h i
  disjoint C j
  disjoint i j
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D j
  disjoint E f
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X j
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( C ` i ) [,) ( D ` i ) ) C_ ( Y ( ball ` ( dist ` ( RR^ ` X ) ) ) E ) )

  proof
    wph
    vf
    cv
    #
    cY
    cE
    cX
    crrx
    cfv
    #
    cds
    cfv
    #
    cbl
    cfv
    co
    #
    wcel
    #
    vf
    vi
    cX
    vi
    cv
    #
    cC
    cfv
    #
    @5
    cD
    cfv
    #
    cico
    co
    #
    cixp
    #
    wral
    @9
    @3
    wss
    wph
    @4
    vf
    @9
    wph
    @0
    @9
    wcel
    #
    wa
    #
    @4
    cY
    @0
    @2
    co
    #
    cE
    clt
    wbr
    #
    @11
    @12
    cX
    @7
    @6
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    csqrt
    cfv
    #
    cE
    @11
    @12
    cX
    @5
    cY
    cfv
    #
    @5
    @0
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    csqrt
    cfv
    #
    cr
    @11
    vg
    vh
    cY
    @0
    cr
    cX
    cmap
    co
    #
    @24
    cX
    @5
    vg
    cv
    #
    cfv
    #
    @5
    vh
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    csqrt
    cfv
    #
    @23
    @2
    cvv
    wph
    @2
    vg
    vh
    @24
    @24
    @32
    cmpt2
    wceq
    #
    @10
    wph
    cX
    cfn
    wcel
    #
    @33
    hoiqssbllem2.x
    @24
    vg
    vh
    vi
    @1
    cX
    @1
    eqid
    @24
    eqid
    #
    rrxdsfi
    syl
    adantr
    @25
    cY
    wceq
    #
    @27
    @0
    wceq
    #
    wa
    #
    @32
    @23
    wceq
    @11
    @38
    @31
    @22
    csqrt
    @38
    cX
    @30
    @21
    vi
    @38
    @29
    @20
    c2
    cexp
    @38
    @26
    @18
    @28
    @19
    cmin
    @36
    @26
    @18
    wceq
    @37
    @5
    @25
    cY
    fveq1
    adantr
    @37
    @28
    @19
    wceq
    @36
    @5
    @27
    @0
    fveq1
    adantl
    oveq12d
    oveq1d
    sumeq2ad
    fveq2d
    adantl
    wph
    cY
    @24
    wcel
    #
    @10
    hoiqssbllem2.y
    adantr
    #
    @11
    @9
    @24
    @0
    wph
    @9
    @24
    wss
    @10
    wph
    @6
    @7
    vi
    cX
    hoiqssbllem2.i
    wph
    cX
    cr
    @5
    cC
    hoiqssbllem2.c
    ffvelrnda
    #
    wph
    @5
    cX
    wcel
    #
    wa
    #
    @7
    wph
    cX
    cr
    @5
    cD
    hoiqssbllem2.d
    ffvelrnda
    #
    rexrd
    #
    hoissrrn2
    adantr
    wph
    @10
    simpr
    sseldd
    #
    @11
    @22
    csqrt
    fvexd
    ovmpt2d
    #
    @11
    @22
    @11
    cX
    @21
    vi
    wph
    @10
    vi
    hoiqssbllem2.i
    vi
    @0
    @9
    vi
    @0
    nfcv
    vi
    cX
    @8
    nfixp1
    nfel
    nfan
    @11
    wph
    @34
    wph
    @10
    simpl
    #
    hoiqssbllem2.x
    syl
    @11
    @42
    wa
    #
    @20
    c2
    @49
    @18
    @19
    @11
    wph
    @42
    @18
    cr
    wcel
    @48
    wph
    cX
    cr
    @5
    cY
    wph
    @39
    cX
    cr
    cY
    wf
    hoiqssbllem2.y
    cY
    cr
    cX
    elmapi
    syl
    ffvelrnda
    #
    sylan
    @49
    @8
    cr
    @19
    wph
    @42
    @8
    cr
    wss
    #
    @10
    @43
    @6
    cr
    wcel
    #
    @7
    cxr
    wcel
    @51
    @41
    @45
    @6
    @7
    icossre
    syl2anc
    adantlr
    @10
    @42
    @19
    @8
    wcel
    #
    wph
    vi
    cX
    @8
    @0
    fvixp2
    adantll
    #
    sseldd
    resubcld
    #
    c2
    cn0
    wcel
    @49
    2nn0
    a1i
    reexpcld
    #
    fsumreclf
    #
    @11
    wph
    @0
    vj
    cX
    vj
    cv
    #
    cC
    cfv
    #
    @58
    cD
    cfv
    #
    cico
    co
    #
    cixp
    #
    wcel
    #
    cc0
    @22
    cle
    wbr
    @48
    @10
    @63
    wph
    @10
    @63
    @9
    @62
    @0
    vi
    vj
    cX
    @8
    @61
    @5
    @58
    wceq
    @6
    @59
    @7
    @60
    cico
    @5
    @58
    cC
    fveq2
    @5
    @58
    cD
    fveq2
    oveq12d
    cbvixpv
    eleq2i
    #
    biimpi
    adantl
    #
    wph
    @63
    wa
    #
    cX
    @21
    vi
    wph
    @34
    @63
    hoiqssbllem2.x
    adantr
    #
    @66
    @42
    wa
    #
    wph
    @10
    @42
    @21
    cr
    wcel
    wph
    @63
    @42
    simpll
    #
    @63
    @10
    wph
    @42
    @10
    @63
    @64
    biimpri
    ad2antlr
    #
    @66
    @42
    simpr
    #
    @56
    syl21anc
    #
    @68
    wph
    @10
    @42
    cc0
    @21
    cle
    wbr
    @69
    @70
    @71
    @49
    @20
    @55
    sqge0d
    syl21anc
    fsumge0
    syl2anc
    #
    resqrtcld
    eqeltrd
    wph
    @17
    cr
    wcel
    @10
    wph
    @16
    wph
    cX
    @15
    vi
    hoiqssbllem2.x
    @43
    @14
    @43
    @7
    @6
    @44
    @41
    resubcld
    #
    resqcld
    #
    fsumrecl
    #
    wph
    cX
    @15
    vi
    hoiqssbllem2.x
    @75
    @43
    @14
    @74
    sqge0d
    fsumge0
    #
    resqrtcld
    adantr
    wph
    cE
    cr
    wcel
    #
    @10
    wph
    cE
    hoiqssbllem2.e
    rpred
    #
    adantr
    #
    @11
    @12
    @23
    @17
    clt
    @47
    @11
    @22
    @16
    clt
    wbr
    #
    @23
    @17
    clt
    wbr
    @11
    wph
    @63
    @81
    @48
    @65
    @66
    cX
    @21
    @15
    vi
    @67
    wph
    cX
    c0
    wne
    #
    @63
    hoiqssbllem2.n
    adantr
    @72
    wph
    @42
    @15
    cr
    wcel
    @63
    @75
    adantlr
    @68
    wph
    @10
    @42
    @21
    @15
    clt
    wbr
    @69
    @70
    @71
    @49
    @20
    @14
    @55
    @49
    @7
    @6
    @11
    wph
    @42
    @7
    cr
    wcel
    #
    @48
    @44
    sylan
    #
    @11
    wph
    @42
    @52
    @48
    @41
    sylan
    #
    resubcld
    @49
    @20
    cabs
    cfv
    #
    @14
    @14
    cabs
    cfv
    #
    clt
    @49
    @52
    @83
    @18
    @8
    wcel
    #
    @53
    @86
    @14
    clt
    wbr
    @85
    @84
    @11
    wph
    @42
    @88
    @48
    @43
    @6
    @7
    @18
    @43
    @6
    @41
    rexrd
    @45
    @43
    @18
    @50
    rexrd
    #
    @43
    @6
    @18
    @41
    @50
    @43
    @18
    cE
    c2
    cX
    chash
    cfv
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    cxr
    wcel
    #
    @18
    cxr
    wcel
    #
    @6
    @94
    @18
    cioo
    co
    wcel
    #
    @6
    @18
    clt
    wbr
    @43
    @94
    @43
    @18
    @93
    @50
    wph
    @93
    cr
    wcel
    @42
    wph
    @93
    wph
    cE
    @92
    hoiqssbllem2.e
    wph
    c2
    @91
    c2
    crp
    wcel
    wph
    2rp
    a1i
    #
    wph
    @90
    wph
    @90
    wph
    @90
    wph
    @90
    cn
    wcel
    #
    @82
    hoiqssbllem2.n
    wph
    @34
    @99
    @82
    wb
    hoiqssbllem2.x
    cX
    hashnncl
    syl
    mpbird
    #
    nnred
    #
    wph
    @90
    @100
    nngt0d
    #
    elrpd
    rpsqrtcld
    #
    rpmulcld
    rpdivcld
    rpred
    adantr
    #
    resubcld
    #
    rexrd
    #
    @89
    hoiqssbllem2.l
    @94
    @18
    @6
    iooltub
    syl3anc
    ltled
    #
    @43
    @96
    @18
    @93
    caddc
    co
    #
    cxr
    wcel
    #
    @7
    @18
    @108
    cioo
    co
    wcel
    #
    @18
    @7
    clt
    wbr
    @89
    @43
    @108
    @43
    @18
    @93
    @50
    @104
    readdcld
    #
    rexrd
    #
    hoiqssbllem2.r
    @18
    @108
    @7
    ioogtlb
    syl3anc
    #
    elicod
    sylan
    @54
    @6
    @7
    @18
    @19
    icodiamlt
    syl22anc
    wph
    @42
    @14
    @87
    wceq
    @10
    @43
    @87
    @14
    @43
    @14
    @74
    @43
    cc0
    @14
    @43
    0red
    @74
    @43
    @6
    @7
    clt
    wbr
    cc0
    @14
    clt
    wbr
    @43
    @6
    @18
    @7
    @41
    @50
    @44
    @107
    @113
    lelttrd
    @43
    @6
    @7
    @41
    @44
    posdifd
    mpbid
    ltled
    #
    absidd
    eqcomd
    adantlr
    breqtrd
    abslt2sqd
    syl21anc
    fsumlt
    syl2anc
    @11
    @22
    @16
    @57
    @73
    @11
    wph
    @16
    cr
    wcel
    @48
    @76
    syl
    @11
    wph
    cc0
    @16
    cle
    wbr
    @48
    @77
    syl
    sqrtltd
    mpbid
    eqbrtrd
    wph
    @17
    cE
    clt
    wbr
    @10
    wph
    @17
    cX
    cE
    @91
    cdiv
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    csqrt
    cfv
    #
    cE
    clt
    wph
    @16
    @117
    clt
    wbr
    @17
    @118
    clt
    wbr
    wph
    cX
    @15
    @116
    vi
    hoiqssbllem2.x
    hoiqssbllem2.n
    @75
    wph
    @116
    cr
    wcel
    @42
    wph
    @115
    wph
    cE
    @91
    @79
    @103
    rerpdivcld
    #
    resqcld
    #
    adantr
    #
    @43
    @14
    @115
    clt
    wbr
    #
    @15
    @116
    clt
    wbr
    #
    @43
    @14
    @108
    @94
    cmin
    co
    #
    @115
    clt
    @43
    @83
    @52
    wa
    #
    @108
    cr
    wcel
    #
    @94
    cr
    wcel
    #
    wa
    #
    wa
    @7
    @108
    clt
    wbr
    #
    @94
    @6
    clt
    wbr
    #
    wa
    @14
    @124
    clt
    wbr
    @43
    @125
    @128
    @43
    @83
    @52
    @44
    @41
    jca
    @43
    @126
    @127
    @111
    @105
    jca
    jca
    @43
    @129
    @130
    @43
    @96
    @109
    @110
    @129
    @89
    @112
    hoiqssbllem2.r
    @18
    @108
    @7
    iooltub
    syl3anc
    @43
    @95
    @96
    @97
    @130
    @106
    @89
    hoiqssbllem2.l
    @94
    @18
    @6
    ioogtlb
    syl3anc
    jca
    @7
    @6
    @108
    @94
    lt2sub
    sylc
    @43
    @124
    @93
    @93
    caddc
    co
    #
    @115
    @43
    @18
    @93
    @93
    @43
    @18
    @50
    recnd
    @43
    @93
    @104
    recnd
    #
    @132
    pnncand
    wph
    @131
    @115
    wceq
    @42
    wph
    @131
    @115
    c2
    cdiv
    co
    #
    @133
    caddc
    co
    @115
    wph
    @93
    @133
    @93
    @133
    caddc
    wph
    @133
    @93
    wph
    cE
    @91
    c2
    wph
    cE
    @79
    recnd
    #
    wph
    @91
    @103
    rpcnd
    #
    wph
    2cnd
    wph
    @91
    @103
    rpne0d
    #
    wph
    c2
    @98
    rpne0d
    divdiv3d
    eqcomd
    #
    @137
    oveq12d
    wph
    @115
    wph
    cE
    @91
    @134
    @135
    @136
    divcld
    2halvesd
    eqtrd
    adantr
    eqtrd
    breqtrd
    @43
    @14
    cr
    wcel
    cc0
    @14
    cle
    wbr
    @115
    cr
    wcel
    #
    cc0
    @115
    cle
    wbr
    #
    @122
    @123
    wb
    @74
    @114
    wph
    @138
    @42
    @119
    adantr
    #
    wph
    @139
    @42
    wph
    cc0
    @115
    wph
    0red
    #
    @119
    wph
    cE
    @91
    @79
    wph
    @91
    @103
    rpred
    wph
    cE
    hoiqssbllem2.e
    rpgt0d
    #
    wph
    @91
    @103
    rpgt0d
    divgt0d
    ltled
    adantr
    @14
    @115
    lt2sq
    syl22anc
    mpbid
    fsumlt
    wph
    @16
    @117
    @76
    @77
    wph
    cX
    @116
    vi
    hoiqssbllem2.x
    @121
    fsumrecl
    wph
    cX
    @116
    vi
    hoiqssbllem2.x
    @121
    @43
    @115
    @140
    sqge0d
    fsumge0
    sqrtltd
    mpbid
    wph
    @118
    cE
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    cE
    cE
    wph
    @117
    @143
    csqrt
    wph
    @117
    @90
    @116
    cmul
    co
    #
    @90
    @143
    @90
    cdiv
    co
    #
    cmul
    co
    @143
    wph
    @34
    @116
    cc
    wcel
    @117
    @145
    wceq
    hoiqssbllem2.x
    wph
    @116
    @120
    recnd
    cX
    @116
    vi
    fsumconst
    syl2anc
    wph
    @116
    @146
    @90
    cmul
    wph
    @116
    @143
    @91
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @146
    wph
    cE
    cc
    wcel
    @91
    cc
    wcel
    @91
    cc0
    wne
    @116
    @148
    wceq
    @134
    @135
    @136
    cE
    @91
    sqdiv
    syl3anc
    wph
    @147
    @90
    @143
    cdiv
    wph
    @90
    cc
    wcel
    @147
    @90
    wceq
    wph
    @90
    @101
    recnd
    #
    @90
    sqrtth
    syl
    oveq2d
    eqtrd
    oveq2d
    wph
    @143
    @90
    wph
    cE
    @134
    sqcld
    @149
    wph
    cc0
    @90
    @141
    @102
    gtned
    divcan2d
    3eqtrd
    fveq2d
    wph
    @78
    cc0
    cE
    cle
    wbr
    @144
    cE
    wceq
    @79
    wph
    cc0
    cE
    @141
    @79
    @142
    ltled
    cE
    sqrtsq
    syl2anc
    wph
    cE
    eqidd
    3eqtrd
    breqtrd
    adantr
    lttrd
    @11
    @2
    @24
    cxmt
    cfv
    wcel
    #
    cE
    cxr
    wcel
    @39
    @0
    @24
    wcel
    @4
    @13
    wb
    wph
    @150
    @10
    wph
    @34
    @2
    @24
    cme
    cfv
    wcel
    @150
    hoiqssbllem2.x
    @2
    cX
    @2
    eqid
    rrxmetfi
    @2
    @24
    metxmet
    3syl
    adantr
    @11
    cE
    @80
    rexrd
    @40
    @11
    @0
    @24
    @24
    @46
    @35
    syl6eleq
    @0
    @2
    cY
    cE
    @24
    elbl2
    syl22anc
    mpbird
    ralrimiva
    vf
    @9
    @3
    dfss3
    sylibr
end
