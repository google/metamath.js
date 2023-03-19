include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cotp.mm"
include "cmmul.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cif.mm"
include "eqid.mm"
include "matmulr.mm"
include "adantr.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "cbs.mm"
include "simplr.mm"
include "simpll.mm"
include "cxp.mm"
include "cmap.mm"
include "dmatmat.mm"
include "imp.mm"
include "matbas2i.mm"
include "syl.mm"
include "adantrr.mm"
include "adantrl.mm"
include "mamuval.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cplusg.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "ad2antlr.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "cvv.mm"
include "c0g.mm"
include "ovexd.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "simp2.mm"
include "simpr.mm"
include "matecl.mm"
include "syl3anc.mm"
include "simplr3.mm"
include "ringcl.mm"
include "simp3.mm"
include "syl6eleq.mm"
include "wi.mm"
include "a1d.mm"
include "imp32.mm"
include "eqtr.mm"
include "ancoms.mm"
include "oveq2d.mm"
include "adantlr.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "gsumdifsnd.mm"
include "wne.mm"
include "simprl.mm"
include "3jca.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "necomd.mm"
include "dmatelnd.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "diffi.mm"
include "ringmnd.mm"
include "anim12ci.mm"
include "gsumz.mm"
include "jca.mm"
include "mndlid.mm"
include "3eqtrd.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "wn.mm"
include "simprr.mm"
include "df-ne.mm"
include "neeq1.mm"
include "biimpcd.mm"
include "sylbir.mm"
include "impcom.mm"
include "ringrz.mm"
include "biimpri.mm"
include "pm2.61ian.mm"
include "anim2i.mm"
include "ancomd.mm"
include "iffalse.mm"
include "mpt2eq3dva.mm"

theorem dmatmul
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let vk: setvar k
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )

  disjoint D x
  disjoint D y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint I i
  disjoint I j
  disjoint J j
  disjoint X i
  disjoint X j
  disjoint .0. i
  disjoint .0. j
  disjoint D k
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint R k
  disjoint X k
  disjoint Y k
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( X e. D /\ Y e. D ) ) -> ( X ( .r ` A ) Y ) = ( x e. N , y e. N |-> if ( x = y , ( ( x X y ) ( .r ` R ) ( x Y y ) ) , .0. ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cA
    cmulr
    cfv
    #
    co
    cX
    cY
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    vx
    vy
    cN
    cN
    cR
    vk
    cN
    vx
    cv
    #
    vk
    cv
    #
    cX
    co
    #
    @10
    vy
    cv
    #
    cY
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
    cmpt2
    vx
    vy
    cN
    cN
    @9
    @12
    wceq
    #
    @9
    @12
    cX
    co
    #
    @9
    @12
    cY
    co
    #
    @14
    co
    #
    c.0
    cif
    #
    cmpt2
    @6
    @7
    @8
    cX
    cY
    @6
    @8
    @7
    @2
    @8
    @7
    wceq
    @5
    cA
    cR
    @8
    cN
    crg
    dmatid.a
    @8
    eqid
    #
    matmulr
    adantr
    eqcomd
    oveqd
    @6
    cR
    cbs
    cfv
    #
    cN
    cR
    @14
    vx
    vk
    vy
    @8
    cN
    cN
    crg
    cX
    cY
    @23
    @24
    eqid
    #
    @14
    eqid
    #
    @0
    @1
    @5
    simplr
    #
    @0
    @1
    @5
    simpll
    #
    @28
    @28
    @2
    @3
    cX
    @24
    cN
    cN
    cxp
    cmap
    co
    #
    wcel
    #
    @4
    @2
    @3
    wa
    cX
    cB
    wcel
    #
    @30
    @2
    @3
    @31
    cA
    cB
    cD
    cR
    cX
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmat
    imp
    #
    cA
    cB
    cR
    @24
    cX
    cN
    dmatid.a
    @25
    dmatid.b
    matbas2i
    syl
    adantrr
    @2
    @4
    cY
    @29
    wcel
    #
    @3
    @2
    @4
    wa
    cY
    cB
    wcel
    #
    @33
    @2
    @4
    @34
    cA
    cB
    cD
    cR
    cY
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmat
    imp
    cA
    cB
    cR
    @24
    cY
    cN
    dmatid.a
    @25
    dmatid.b
    matbas2i
    syl
    adantrl
    mamuval
    @6
    vx
    vy
    cN
    cN
    @17
    @22
    @18
    @6
    @9
    cN
    wcel
    #
    @12
    cN
    wcel
    #
    w3a
    #
    @17
    @22
    wceq
    @18
    @37
    wa
    #
    @17
    @21
    @22
    @38
    @17
    cR
    vk
    cN
    @9
    csn
    #
    cdif
    #
    @15
    cmpt
    #
    cgsu
    co
    #
    @21
    cR
    cplusg
    cfv
    #
    co
    c.0
    @21
    @43
    co
    #
    @21
    @38
    cN
    @24
    @43
    vk
    cR
    @9
    cfn
    @15
    @21
    @25
    @43
    eqid
    #
    @37
    cR
    ccmn
    wcel
    #
    @18
    @6
    @35
    @46
    @36
    @1
    @46
    @0
    @5
    cR
    ringcmn
    ad2antlr
    3ad2ant1
    adantl
    @37
    @0
    @18
    @6
    @35
    @0
    @36
    @28
    3ad2ant1
    adantl
    #
    @38
    vk
    cN
    @16
    cvv
    cvv
    @15
    cR
    c0g
    cfv
    @16
    eqid
    @47
    @38
    @10
    cN
    wcel
    #
    wa
    #
    @11
    @13
    @14
    ovexd
    @38
    cR
    c0g
    fvexd
    fsuppmptdm
    @49
    @1
    @11
    @24
    wcel
    #
    @13
    @24
    wcel
    #
    @15
    @24
    wcel
    @37
    @1
    @18
    @48
    @6
    @35
    @1
    @36
    @27
    3ad2ant1
    #
    ad2antlr
    @49
    @35
    @48
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    @50
    @37
    @35
    @18
    @48
    @6
    @35
    @36
    simp2
    #
    ad2antlr
    @38
    @48
    simpr
    #
    @37
    @54
    @18
    @48
    @6
    @35
    @54
    @36
    @2
    @3
    @54
    @4
    @2
    @3
    @54
    cA
    @53
    cD
    cR
    cX
    cN
    crg
    c.0
    dmatid.a
    @53
    eqid
    #
    dmatid.0
    dmatid.d
    dmatmat
    imp
    adantrr
    3ad2ant1
    ad2antlr
    cA
    cR
    @9
    @10
    @24
    cX
    cN
    dmatid.a
    @25
    matecl
    #
    syl3anc
    @49
    @48
    @36
    cY
    @53
    wcel
    #
    @51
    @56
    @6
    @35
    @36
    @18
    @48
    simplr3
    @37
    @59
    @18
    @48
    @6
    @35
    @59
    @36
    @2
    @4
    @59
    @3
    @2
    @4
    @59
    cA
    @53
    cD
    cR
    cY
    cN
    crg
    c.0
    dmatid.a
    @57
    dmatid.0
    dmatid.d
    dmatmat
    #
    imp
    adantrl
    3ad2ant1
    #
    ad2antlr
    cA
    cR
    @10
    @12
    @24
    cY
    cN
    dmatid.a
    @25
    matecl
    #
    syl3anc
    @24
    cR
    @14
    @11
    @13
    @25
    @26
    ringcl
    syl3anc
    @37
    @35
    @18
    @55
    adantl
    @37
    @21
    @24
    wcel
    #
    @18
    @37
    @1
    @19
    @24
    wcel
    #
    @20
    @24
    wcel
    #
    @63
    @52
    @37
    @35
    @36
    @54
    @64
    @55
    @6
    @35
    @36
    simp3
    #
    @6
    @35
    @54
    @36
    @6
    cX
    cB
    @53
    @2
    @3
    @31
    @4
    @32
    adantrr
    dmatid.b
    syl6eleq
    3ad2ant1
    #
    cA
    cR
    @9
    @12
    @24
    cX
    cN
    dmatid.a
    @25
    matecl
    syl3anc
    #
    @37
    @35
    @36
    @59
    @65
    @55
    @66
    @6
    @35
    @59
    @36
    @2
    @3
    @4
    @59
    @2
    @4
    @59
    wi
    @3
    @60
    a1d
    imp32
    3ad2ant1
    #
    cA
    cR
    @9
    @12
    @24
    cY
    cN
    dmatid.a
    @25
    matecl
    #
    syl3anc
    @24
    cR
    @14
    @19
    @20
    @25
    @26
    ringcl
    #
    syl3anc
    adantl
    @38
    @10
    @9
    wceq
    #
    wa
    @11
    @19
    @13
    @20
    @14
    @18
    @72
    @11
    @19
    wceq
    @37
    @18
    @72
    wa
    @10
    @12
    @9
    cX
    @72
    @18
    @10
    @12
    wceq
    @10
    @9
    @12
    eqtr
    ancoms
    oveq2d
    adantlr
    @72
    @13
    @20
    wceq
    @38
    @10
    @9
    @12
    cY
    oveq1
    adantl
    oveq12d
    gsumdifsnd
    @38
    @42
    c.0
    @21
    @43
    @38
    @42
    cR
    vk
    @40
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @38
    @41
    @73
    cR
    cgsu
    @38
    vk
    @40
    @15
    c.0
    @38
    @10
    @40
    wcel
    #
    wa
    #
    @15
    c.0
    @13
    @14
    co
    #
    c.0
    @76
    @11
    c.0
    @13
    @14
    @76
    @0
    @1
    @3
    w3a
    #
    @35
    @48
    @9
    @10
    wne
    #
    @11
    c.0
    wceq
    #
    @37
    @78
    @18
    @75
    @6
    @35
    @78
    @36
    @6
    @0
    @1
    @3
    @28
    @27
    @2
    @3
    @4
    simprl
    3jca
    3ad2ant1
    #
    ad2antlr
    @37
    @35
    @18
    @75
    @55
    ad2antlr
    @75
    @48
    @38
    @10
    cN
    @39
    eldifi
    adantl
    #
    @75
    @79
    @38
    @75
    @10
    @9
    @10
    cN
    @9
    eldifsni
    necomd
    adantl
    cA
    cB
    cD
    cR
    @9
    @10
    cN
    cX
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatelnd
    #
    syl13anc
    oveq1d
    @76
    @1
    @51
    @77
    c.0
    wceq
    #
    @37
    @1
    @18
    @75
    @52
    ad2antlr
    @76
    @48
    @36
    @59
    @51
    @82
    @6
    @35
    @36
    @18
    @75
    simplr3
    @37
    @59
    @18
    @75
    @61
    ad2antlr
    @62
    syl3anc
    @24
    cR
    @14
    @13
    c.0
    @25
    @26
    dmatid.0
    ringlz
    #
    syl2anc
    eqtrd
    mpteq2dva
    oveq2d
    @38
    cR
    cmnd
    wcel
    #
    @40
    cfn
    wcel
    #
    wa
    #
    @74
    c.0
    wceq
    @37
    @88
    @18
    @6
    @35
    @88
    @36
    @2
    @88
    @5
    @0
    @87
    @1
    @86
    cN
    @39
    diffi
    cR
    ringmnd
    #
    anim12ci
    adantr
    3ad2ant1
    adantl
    @40
    vk
    cR
    cfn
    c.0
    dmatid.0
    gsumz
    syl
    eqtrd
    oveq1d
    @38
    @86
    @63
    wa
    #
    @44
    @21
    wceq
    @37
    @90
    @18
    @37
    @86
    @63
    @6
    @35
    @86
    @36
    @1
    @86
    @0
    @5
    @89
    ad2antlr
    3ad2ant1
    @37
    @1
    @64
    @65
    @63
    @52
    @68
    @37
    @35
    @36
    @59
    @65
    @55
    @66
    @61
    @70
    syl3anc
    @71
    syl3anc
    jca
    adantl
    @24
    @43
    cR
    @21
    c.0
    @25
    @45
    dmatid.0
    mndlid
    syl
    3eqtrd
    @18
    @22
    @21
    wceq
    @37
    @18
    @21
    c.0
    iftrue
    adantr
    eqtr4d
    @18
    wn
    #
    @37
    wa
    #
    @17
    cR
    vk
    cN
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @22
    @92
    @16
    @93
    cR
    cgsu
    @92
    vk
    cN
    @15
    c.0
    @9
    @10
    wceq
    #
    @92
    @48
    wa
    #
    @15
    c.0
    wceq
    @95
    @96
    wa
    #
    @15
    @11
    c.0
    @14
    co
    #
    c.0
    @97
    @13
    c.0
    @11
    @14
    @97
    @0
    @1
    @4
    w3a
    #
    @48
    @36
    @10
    @12
    wne
    #
    @13
    c.0
    wceq
    @96
    @99
    @95
    @37
    @99
    @91
    @48
    @6
    @35
    @99
    @36
    @6
    @0
    @1
    @4
    @28
    @27
    @2
    @3
    @4
    simprr
    3jca
    3ad2ant1
    ad2antlr
    adantl
    @95
    @92
    @48
    simprr
    @96
    @36
    @95
    @6
    @35
    @36
    @91
    @48
    simplr3
    #
    adantl
    @96
    @95
    @100
    @92
    @95
    @100
    wi
    #
    @48
    @91
    @102
    @37
    @91
    @9
    @12
    wne
    #
    @102
    @9
    @12
    df-ne
    @95
    @103
    @100
    @9
    @10
    @12
    neeq1
    biimpcd
    sylbir
    adantr
    adantr
    impcom
    cA
    cB
    cD
    cR
    @10
    @12
    cN
    cY
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatelnd
    syl13anc
    oveq2d
    @96
    @98
    c.0
    wceq
    #
    @95
    @96
    @1
    @50
    @104
    @37
    @1
    @91
    @48
    @52
    ad2antlr
    #
    @96
    @35
    @48
    @54
    @50
    @37
    @35
    @91
    @48
    @55
    ad2antlr
    #
    @92
    @48
    simpr
    #
    @37
    @54
    @91
    @48
    @67
    ad2antlr
    @58
    syl3anc
    @24
    cR
    @14
    @11
    c.0
    @25
    @26
    dmatid.0
    ringrz
    syl2anc
    adantl
    eqtrd
    @95
    wn
    #
    @96
    wa
    #
    @15
    @77
    c.0
    @109
    @11
    c.0
    @13
    @14
    @109
    @78
    @35
    @48
    @79
    @80
    @96
    @78
    @108
    @37
    @78
    @91
    @48
    @81
    ad2antlr
    adantl
    @96
    @35
    @108
    @106
    adantl
    @108
    @92
    @48
    simprr
    @108
    @79
    @96
    @79
    @108
    @9
    @10
    df-ne
    biimpri
    adantr
    @83
    syl13anc
    oveq1d
    @96
    @84
    @108
    @96
    @1
    @51
    @84
    @105
    @96
    @48
    @36
    @59
    @51
    @107
    @101
    @37
    @59
    @91
    @48
    @69
    ad2antlr
    @62
    syl3anc
    @85
    syl2anc
    adantl
    eqtrd
    pm2.61ian
    mpteq2dva
    oveq2d
    @37
    @94
    c.0
    wceq
    #
    @91
    @6
    @35
    @110
    @36
    @2
    @110
    @5
    @2
    @86
    @0
    wa
    @110
    @2
    @0
    @86
    @1
    @86
    @0
    @89
    anim2i
    ancomd
    cN
    vk
    cR
    cfn
    c.0
    dmatid.0
    gsumz
    syl
    adantr
    3ad2ant1
    adantl
    @91
    c.0
    @22
    wceq
    @37
    @91
    @22
    c.0
    @18
    @21
    c.0
    iffalse
    eqcomd
    adantr
    3eqtrd
    pm2.61ian
    mpt2eq3dva
    3eqtrd
end
