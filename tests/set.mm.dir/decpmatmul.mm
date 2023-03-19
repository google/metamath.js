include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cdecpmat.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "wral.mm"
include "cmpt2.mm"
include "cvv.mm"
include "eqidd.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "cotp.mm"
include "cmmul.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "anim2i.mm"
include "ancomd.mm"
include "3adant3.mm"
include "eqid.mm"
include "matmulr.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "cbs.mm"
include "simp1.mm"
include "cxp.mm"
include "cmap.mm"
include "simpl2l.mm"
include "elfznn0.mm"
include "3jca.mm"
include "decpmatcl.mm"
include "matbas2i.mm"
include "simpl2r.mm"
include "fznn0sub.mm"
include "mamuval.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "c0g.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "simpr.mm"
include "matecld.mm"
include "simpl3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "matbas2d.mm"
include "fzfid.mm"
include "simpl.mm"
include "jca.mm"
include "3ad2ant2.mm"
include "mpt2exga.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "matgsum.mm"
include "cco1.mm"
include "decpmatmullem.mm"
include "syl213anc.mm"
include "simpll1.mm"
include "simplrl.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "matecl.mm"
include "ad2antll.mm"
include "coe1fvalcl.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "gsumcom3fi.mm"
include "anim1i.mm"
include "decpmate.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "pmatring.mm"
include "syld3an2.mm"
include "matring.mm"
include "eqmat.mm"
include "mpbird.mm"

theorem decpmatmul
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cU: class U
  let vk: setvar k
  let cK: class K
  let cN: class N
  let cW: class W
  let vt: setvar t
  let cI: class I
  let vl: setvar l
  let cJ: class J
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume decpmatmul.p: |- P = ( Poly1 ` R )
  assume decpmatmul.c: |- C = ( N Mat P )
  assume decpmatmul.b: |- B = ( Base ` C )
  assume decpmatmul.a: |- A = ( N Mat R )

  disjoint B k
  disjoint K k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint U k
  disjoint W k
  disjoint A k
  disjoint B t
  disjoint k t
  disjoint I k
  disjoint I l
  disjoint I t
  disjoint k l
  disjoint l t
  disjoint J k
  disjoint J l
  disjoint J t
  disjoint K l
  disjoint K t
  disjoint N t
  disjoint P t
  disjoint R l
  disjoint R t
  disjoint U l
  disjoint U t
  disjoint W l
  disjoint W t
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint B i
  disjoint B j
  disjoint B x
  disjoint B y
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint C i
  disjoint C j
  disjoint K i
  disjoint K j
  disjoint K x
  disjoint K y
  disjoint N i
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint R i
  disjoint R j
  disjoint R x
  disjoint R y
  disjoint U i
  disjoint U j
  disjoint U x
  disjoint U y
  disjoint W i
  disjoint W j
  disjoint W x
  disjoint W y
  assert |- ( ( R e. Ring /\ ( U e. B /\ W e. B ) /\ K e. NN0 ) -> ( ( U ( .r ` C ) W ) decompPMat K ) = ( A gsum ( k e. ( 0 ... K ) |-> ( ( U decompPMat k ) ( .r ` A ) ( W decompPMat ( K - k ) ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cU
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    cU
    cW
    cC
    cmulr
    cfv
    #
    co
    #
    cK
    cdecpmat
    co
    #
    cA
    vk
    cc0
    cK
    cfz
    co
    #
    cU
    vk
    cv
    #
    cdecpmat
    co
    #
    cW
    cK
    @10
    cmin
    co
    #
    cdecpmat
    co
    #
    cA
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    @8
    co
    #
    @19
    @20
    @17
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @5
    @23
    vi
    vj
    cN
    cN
    @5
    @19
    cN
    wcel
    #
    @20
    cN
    wcel
    #
    wa
    #
    wa
    #
    @19
    @20
    vx
    vy
    cN
    cN
    cR
    vk
    @9
    cR
    vt
    cN
    vx
    cv
    #
    vt
    cv
    #
    @11
    co
    #
    @30
    vy
    cv
    #
    @13
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    co
    cR
    vk
    @9
    cR
    vt
    cN
    @19
    @30
    @11
    co
    #
    @30
    @20
    @13
    co
    #
    @34
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @22
    @21
    @28
    vx
    vy
    @19
    @20
    cN
    cN
    @39
    @47
    @40
    cvv
    @28
    @40
    eqidd
    @29
    @19
    wceq
    #
    @32
    @20
    wceq
    #
    wa
    #
    @39
    @47
    wceq
    @28
    @50
    @38
    @46
    cR
    cgsu
    @50
    vk
    @9
    @37
    @45
    @50
    @36
    @44
    cR
    cgsu
    @50
    vt
    cN
    @35
    @43
    @48
    @49
    @31
    @41
    @33
    @42
    @34
    @29
    @19
    @30
    @11
    oveq1
    @32
    @20
    @30
    @13
    oveq2
    oveqan12d
    mpteq2dv
    oveq2d
    mpteq2dv
    oveq2d
    adantl
    @5
    @25
    @26
    simprl
    #
    @5
    @25
    @26
    simprr
    #
    @28
    cR
    @46
    cgsu
    ovexd
    ovmpt2d
    @28
    @17
    @40
    @19
    @20
    @28
    @17
    cA
    vk
    @9
    vx
    vy
    cN
    cN
    @37
    cmpt2
    #
    cmpt
    #
    cgsu
    co
    @40
    @28
    @16
    @54
    cA
    cgsu
    @28
    vk
    @9
    @15
    @53
    @28
    @10
    @9
    wcel
    #
    wa
    #
    @15
    @11
    @13
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    @53
    @56
    @14
    @57
    @11
    @13
    @56
    @57
    @14
    @28
    @57
    @14
    wceq
    #
    @55
    @5
    @58
    @27
    @5
    cN
    cfn
    wcel
    #
    @0
    wa
    #
    @58
    @0
    @3
    @60
    @4
    @0
    @3
    wa
    #
    @0
    @59
    @3
    @59
    @0
    @1
    @59
    @2
    @1
    @59
    cP
    cvv
    wcel
    #
    cC
    cB
    cP
    cN
    cU
    decpmatmul.c
    decpmatmul.b
    matrcl
    #
    simpld
    adantr
    anim2i
    ancomd
    #
    3adant3
    #
    cA
    cR
    @57
    cN
    crg
    decpmatmul.a
    @57
    eqid
    #
    matmulr
    syl
    adantr
    adantr
    eqcomd
    oveqd
    @56
    cR
    cbs
    cfv
    #
    cN
    cR
    @34
    vx
    vt
    vy
    @57
    cN
    cN
    crg
    @11
    @13
    @66
    @67
    eqid
    #
    @34
    eqid
    #
    @28
    @0
    @55
    @5
    @0
    @27
    @0
    @3
    @4
    simp1
    #
    adantr
    #
    adantr
    #
    @28
    @59
    @55
    @5
    @59
    @27
    @5
    @59
    @0
    @65
    simpld
    adantr
    #
    adantr
    #
    @74
    @74
    @56
    @11
    cA
    cbs
    cfv
    #
    wcel
    #
    @11
    @67
    cN
    cN
    cxp
    cmap
    co
    #
    wcel
    @56
    @0
    @1
    @10
    cn0
    wcel
    #
    w3a
    #
    @76
    @56
    @0
    @1
    @78
    @72
    @28
    @1
    @55
    @1
    @2
    @0
    @4
    @27
    simpl2l
    adantr
    @55
    @78
    @28
    @10
    cK
    elfznn0
    #
    adantl
    3jca
    #
    cA
    cB
    cC
    @75
    cP
    cR
    @10
    cU
    cN
    crg
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmatmul.a
    @75
    eqid
    #
    decpmatcl
    #
    syl
    cA
    @75
    cR
    @67
    @11
    cN
    decpmatmul.a
    @68
    @82
    matbas2i
    syl
    @56
    @13
    @75
    wcel
    #
    @13
    @77
    wcel
    @56
    @0
    @2
    @12
    cn0
    wcel
    #
    w3a
    #
    @84
    @56
    @0
    @2
    @85
    @72
    @28
    @2
    @55
    @1
    @2
    @0
    @4
    @27
    simpl2r
    #
    adantr
    @55
    @85
    @28
    @10
    cc0
    cK
    fznn0sub
    #
    adantl
    3jca
    #
    cA
    cB
    cC
    @75
    cP
    cR
    @12
    cW
    cN
    crg
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmatmul.a
    @82
    decpmatcl
    #
    syl
    #
    cA
    @75
    cR
    @67
    @13
    cN
    decpmatmul.a
    @68
    @82
    matbas2i
    syl
    mamuval
    eqtrd
    mpteq2dva
    oveq2d
    @28
    vk
    cA
    @75
    cR
    @37
    vx
    vy
    @9
    cN
    cvv
    cA
    c0g
    cfv
    #
    decpmatmul.a
    @82
    @92
    eqid
    @73
    @28
    cc0
    cK
    cfz
    ovexd
    @71
    @56
    vx
    vy
    cA
    @75
    @37
    cR
    @67
    cN
    crg
    decpmatmul.a
    @68
    @82
    @74
    @72
    @56
    @29
    cN
    wcel
    #
    @32
    cN
    wcel
    #
    w3a
    #
    @67
    vt
    cR
    cN
    @35
    @68
    @56
    @93
    cR
    ccmn
    wcel
    #
    @94
    @28
    @96
    @55
    @5
    @96
    @27
    @5
    @0
    @96
    @70
    cR
    ringcmn
    syl
    adantr
    #
    adantr
    3ad2ant1
    @56
    @93
    @59
    @94
    @74
    3ad2ant1
    @95
    @35
    @67
    wcel
    #
    vt
    cN
    @95
    @30
    cN
    wcel
    #
    wa
    #
    @0
    @31
    @67
    wcel
    @33
    @67
    wcel
    @98
    @95
    @0
    @99
    @56
    @93
    @0
    @94
    @72
    3ad2ant1
    adantr
    @100
    cA
    @75
    cR
    @29
    @30
    @67
    @11
    cN
    decpmatmul.a
    @68
    @82
    @56
    @93
    @94
    @99
    simpl2
    @95
    @99
    simpr
    #
    @100
    @79
    @76
    @95
    @79
    @99
    @56
    @93
    @79
    @94
    @81
    3ad2ant1
    adantr
    @83
    syl
    matecld
    @100
    cA
    @75
    cR
    @30
    @32
    @67
    @13
    cN
    decpmatmul.a
    @68
    @82
    @101
    @56
    @93
    @94
    @99
    simpl3
    @95
    @84
    @99
    @56
    @93
    @84
    @94
    @91
    3ad2ant1
    adantr
    matecld
    @67
    cR
    @34
    @31
    @33
    @68
    @69
    ringcl
    syl3anc
    ralrimiva
    gsummptcl
    matbas2d
    @28
    vk
    @9
    @54
    cvv
    cvv
    @53
    @92
    @54
    eqid
    @28
    cc0
    cK
    fzfid
    #
    @56
    @59
    @59
    wa
    #
    @53
    cvv
    wcel
    @28
    @103
    @55
    @5
    @103
    @27
    @3
    @0
    @103
    @4
    @1
    @103
    @2
    @1
    @59
    @62
    wa
    #
    @103
    @63
    @104
    @59
    @59
    @59
    @62
    simpl
    #
    @105
    jca
    syl
    adantr
    3ad2ant2
    adantr
    adantr
    vx
    vy
    cN
    cN
    @37
    cfn
    cfn
    mpt2exga
    syl
    @28
    cA
    c0g
    fvexd
    fsuppmptdm
    matgsum
    eqtrd
    oveqd
    @28
    @21
    cR
    vt
    cN
    cR
    vk
    @9
    @10
    @19
    @30
    cU
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @12
    @30
    @20
    cW
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @34
    co
    #
    cmpt
    cgsu
    co
    cmpt
    cgsu
    co
    #
    cR
    vk
    @9
    cR
    vt
    cN
    @112
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    @47
    @28
    @59
    @0
    @3
    @25
    @26
    @4
    @21
    @113
    wceq
    @73
    @71
    @0
    @3
    @4
    @27
    simpl2
    @51
    @52
    @0
    @3
    @4
    @27
    simpl3
    vt
    cB
    cC
    cP
    cR
    cU
    @19
    @20
    cK
    cN
    cW
    vk
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmatmullem
    syl213anc
    @28
    cN
    @67
    @9
    vt
    vk
    cR
    @112
    @68
    @97
    @73
    @102
    @28
    @99
    @55
    wa
    #
    wa
    #
    @0
    @108
    @67
    wcel
    #
    @111
    @67
    wcel
    #
    @112
    @67
    wcel
    @0
    @3
    @4
    @27
    @117
    simpll1
    @118
    @106
    cP
    cbs
    cfv
    #
    wcel
    #
    @78
    @119
    @118
    @25
    @99
    cU
    cC
    cbs
    cfv
    #
    wcel
    #
    @122
    @5
    @25
    @26
    @117
    simplrl
    @28
    @99
    @55
    simprl
    #
    @28
    @124
    @117
    @5
    @124
    @27
    @3
    @0
    @124
    @4
    @1
    @124
    @2
    @1
    @124
    cB
    @123
    cU
    decpmatmul.b
    eleq2i
    biimpi
    adantr
    3ad2ant2
    adantr
    adantr
    cC
    cP
    @19
    @30
    @121
    cU
    cN
    decpmatmul.c
    @121
    eqid
    #
    matecl
    syl3anc
    @55
    @78
    @28
    @99
    @80
    ad2antll
    @107
    @121
    cP
    cR
    @106
    @67
    @10
    @107
    eqid
    @126
    decpmatmul.p
    @68
    coe1fvalcl
    syl2anc
    @118
    @109
    @121
    wcel
    @85
    @120
    @118
    cC
    cB
    cP
    @30
    @20
    @121
    cW
    cN
    decpmatmul.c
    @126
    decpmatmul.b
    @125
    @5
    @25
    @26
    @117
    simplrr
    @28
    @2
    @117
    @87
    adantr
    matecld
    @55
    @85
    @28
    @99
    @88
    ad2antll
    @110
    @121
    cP
    cR
    @109
    @67
    @12
    @110
    eqid
    @126
    decpmatmul.p
    @68
    coe1fvalcl
    syl2anc
    @67
    cR
    @34
    @108
    @111
    @68
    @69
    ringcl
    syl3anc
    gsumcom3fi
    @28
    @116
    @46
    cR
    cgsu
    @28
    vk
    @9
    @115
    @45
    @56
    @114
    @44
    cR
    cgsu
    @56
    vt
    cN
    @112
    @43
    @56
    @99
    wa
    #
    @43
    @112
    @127
    @41
    @108
    @42
    @111
    @34
    @127
    @79
    @25
    @99
    wa
    @41
    @108
    wceq
    @56
    @79
    @99
    @81
    adantr
    @56
    @25
    @99
    @28
    @25
    @55
    @51
    adantr
    anim1i
    cB
    cC
    cP
    cR
    @19
    @30
    @10
    cU
    cN
    crg
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmate
    syl2anc
    @127
    @86
    @99
    @26
    wa
    @42
    @111
    wceq
    @56
    @86
    @99
    @89
    adantr
    @127
    @26
    @99
    @56
    @26
    @99
    @5
    @25
    @26
    @55
    simplrr
    anim1i
    ancomd
    cB
    cC
    cP
    cR
    @30
    @20
    @12
    cW
    cN
    crg
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmate
    syl2anc
    oveq12d
    eqcomd
    mpteq2dva
    oveq2d
    mpteq2dva
    oveq2d
    3eqtrd
    3eqtr4rd
    ralrimivva
    @5
    @8
    @75
    wcel
    #
    @17
    @75
    wcel
    @18
    @24
    wb
    @0
    @7
    cB
    wcel
    #
    @3
    @4
    @128
    @0
    @3
    @129
    @4
    @61
    cC
    crg
    wcel
    #
    @1
    @2
    @129
    @61
    @60
    @130
    @64
    cC
    cP
    cR
    cN
    decpmatmul.p
    decpmatmul.c
    pmatring
    syl
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    cB
    cC
    @6
    cU
    cW
    decpmatmul.b
    @6
    eqid
    ringcl
    syl3anc
    3adant3
    cA
    cB
    cC
    @75
    cP
    cR
    cK
    @7
    cN
    crg
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmatmul.a
    @82
    decpmatcl
    syld3an2
    @5
    @75
    vk
    cA
    @9
    @15
    @82
    @5
    cA
    crg
    wcel
    #
    cA
    ccmn
    wcel
    @5
    @60
    @131
    @65
    cA
    cR
    cN
    decpmatmul.a
    matring
    syl
    #
    cA
    ringcmn
    syl
    @5
    cc0
    cK
    fzfid
    @5
    @15
    @75
    wcel
    #
    vk
    @9
    @5
    @55
    wa
    #
    @131
    @76
    @84
    @133
    @5
    @131
    @55
    @132
    adantr
    @134
    @79
    @76
    @134
    @0
    @1
    @78
    @5
    @0
    @55
    @70
    adantr
    #
    @1
    @2
    @0
    @4
    @55
    simpl2l
    @55
    @78
    @5
    @80
    adantl
    3jca
    @83
    syl
    @134
    @86
    @84
    @134
    @0
    @2
    @85
    @135
    @1
    @2
    @0
    @4
    @55
    simpl2r
    @55
    @85
    @5
    @88
    adantl
    3jca
    @90
    syl
    @75
    cA
    @14
    @11
    @13
    @82
    @14
    eqid
    ringcl
    syl3anc
    ralrimiva
    gsummptcl
    cA
    @75
    cR
    vi
    vj
    cN
    @8
    @17
    decpmatmul.a
    @82
    eqmat
    syl2anc
    mpbird
end
