include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "wceq.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wa.mm"
include "id.mm"
include "crg.mm"
include "simp1.mm"
include "ad2antrr.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "matring.mm"
include "sylan2.mm"
include "ringcmn.mm"
include "syl.mm"
include "3adant3.mm"
include "nn0ex.mm"
include "a1i.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "simpll3.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "ccpmat.mm"
include "wf.mm"
include "cpm2mf.mm"
include "simplr.mm"
include "chfacfisfcpmat.mm"
include "syl32anc.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "fmptd.mm"
include "fvexd.mm"
include "ovexd.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clt.mm"
include "csb.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "chfacffsupp.mm"
include "anassrs.mm"
include "wb.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "fvex.mm"
include "fsuppmapnn0ub.mm"
include "sylancl.mm"
include "csbov12g.mm"
include "csbov1g.mm"
include "csbvarg.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "csbfv2g.mm"
include "csbfv.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ad2antlr.mm"
include "fveq2.mm"
include "jca.mm"
include "m2cpminv0.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "3eqtrd.mm"
include "ex.mm"
include "adantlr.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "syld.mm"
include "mpd.mm"
include "mptnn0fsupp.mm"
include "gsumcl.mm"
include "m2cpminvid.mm"
include "pmatring.mm"
include "ringmnd.mm"
include "cghm.mm"
include "cmhm.mm"
include "mat2pmatghm.mm"
include "ghmmhm.mm"
include "gsummptmhm.mm"
include "crh.mm"
include "mat2pmatrhm.mm"
include "rhmmul.mm"
include "mat2pmatmhm.mm"
include "mhmmulg.mm"
include "m2cpminvid2.mm"
include "mpteq2dva.mm"
include "eqtr3d.mm"
include "cayhamlem3.mm"
include "reximddv2.mm"

theorem cayhamlem4
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cG: class G
  let c.as: class .*
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vl: setvar l
  let vw: setvar w
  let vz: setvar z
  assume chcoeffeq.a: |- A = ( N Mat R )
  assume chcoeffeq.b: |- B = ( Base ` A )
  assume chcoeffeq.p: |- P = ( Poly1 ` R )
  assume chcoeffeq.y: |- Y = ( N Mat P )
  assume chcoeffeq.r: |- .X. = ( .r ` Y )
  assume chcoeffeq.s: |- .- = ( -g ` Y )
  assume chcoeffeq.0: |- .0. = ( 0g ` Y )
  assume chcoeffeq.t: |- T = ( N matToPolyMat R )
  assume chcoeffeq.c: |- C = ( N CharPlyMat R )
  assume chcoeffeq.k: |- K = ( C ` M )
  assume chcoeffeq.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chcoeffeq.w: |- W = ( Base ` Y )
  assume chcoeffeq.1: |- .1. = ( 1r ` A )
  assume chcoeffeq.m: |- .* = ( .s ` A )
  assume chcoeffeq.u: |- U = ( N cPolyMatToMat R )
  assume cayhamlem.e1: |- .^ = ( .g ` ( mulGrp ` A ) )
  assume cayhamlem.e2: |- E = ( .g ` ( mulGrp ` Y ) )

  disjoint A n
  disjoint B n
  disjoint G n
  disjoint K n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint U n
  disjoint Y n
  disjoint .1. n
  disjoint .* n
  disjoint b n
  disjoint n s
  disjoint A b
  disjoint A s
  disjoint b s
  disjoint B b
  disjoint B s
  disjoint M b
  disjoint M s
  disjoint N b
  disjoint N s
  disjoint P b
  disjoint P n
  disjoint P s
  disjoint R b
  disjoint R s
  disjoint T b
  disjoint T n
  disjoint T s
  disjoint W n
  disjoint Y b
  disjoint Y s
  disjoint .0. n
  disjoint .X. n
  disjoint .- b
  disjoint .- n
  disjoint .- s
  disjoint .^ n
  disjoint A l
  disjoint l n
  disjoint B l
  disjoint G l
  disjoint K l
  disjoint M l
  disjoint N l
  disjoint R l
  disjoint U l
  disjoint .1. l
  disjoint .* l
  disjoint b l
  disjoint l s
  disjoint A w
  disjoint A z
  disjoint b w
  disjoint b z
  disjoint s w
  disjoint s z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint G w
  disjoint G z
  disjoint M w
  disjoint M z
  disjoint N w
  disjoint N z
  disjoint R w
  disjoint R z
  disjoint U w
  disjoint U z
  disjoint Y w
  disjoint Y z
  disjoint .^ w
  disjoint .^ z
  disjoint n w
  disjoint n z
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN E. b e. ( B ^m ( 0 ... s ) ) ( A gsum ( n e. NN0 |-> ( ( ( coe1 ` K ) ` n ) .* ( n .^ M ) ) ) ) = ( U ` ( Y gsum ( n e. NN0 |-> ( ( n E ( T ` M ) ) .X. ( G ` n ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cA
    vn
    cn0
    vn
    cv
    #
    cK
    cco1
    cfv
    cfv
    @4
    cM
    c.ex
    co
    #
    c.as
    co
    cmpt
    cgsu
    co
    #
    cA
    vn
    cn0
    @5
    @4
    cG
    cfv
    #
    cU
    cfv
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
    @6
    cY
    vn
    cn0
    @4
    cM
    cT
    cfv
    cE
    co
    #
    @7
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cU
    cfv
    #
    wceq
    vs
    vb
    cn
    cB
    cc0
    vs
    cv
    #
    cfz
    co
    cmap
    co
    #
    @13
    @3
    @19
    cn
    wcel
    #
    wa
    #
    vb
    cv
    @20
    wcel
    #
    wa
    #
    @6
    @12
    @18
    @13
    id
    @24
    @12
    cT
    cfv
    #
    cU
    cfv
    #
    @12
    @18
    @24
    @0
    cR
    crg
    wcel
    #
    @12
    cB
    wcel
    @26
    @12
    wceq
    @3
    @0
    @21
    @23
    @0
    @1
    @2
    simp1
    #
    ad2antrr
    #
    @3
    @27
    @21
    @23
    @1
    @0
    @27
    @2
    cR
    crngring
    #
    3ad2ant2
    #
    ad2antrr
    #
    @24
    cn0
    cB
    @11
    cA
    cvv
    cA
    c0g
    cfv
    #
    chcoeffeq.b
    @33
    eqid
    #
    @3
    cA
    ccmn
    wcel
    #
    @21
    @23
    @0
    @1
    @35
    @2
    @0
    @1
    wa
    cA
    crg
    wcel
    #
    @35
    @1
    @0
    @27
    @36
    @30
    cA
    cR
    cN
    chcoeffeq.a
    matring
    #
    sylan2
    cA
    ringcmn
    syl
    3adant3
    ad2antrr
    #
    cn0
    cvv
    wcel
    #
    @24
    nn0ex
    a1i
    #
    @24
    vn
    cn0
    @10
    cB
    @11
    @24
    @4
    cn0
    wcel
    #
    wa
    #
    @36
    @5
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @24
    @36
    @41
    @24
    @0
    @27
    @36
    @29
    @32
    @37
    syl2anc
    #
    adantr
    @42
    cA
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @41
    @2
    @43
    @3
    @48
    @21
    @23
    @41
    @3
    @36
    @48
    @3
    @0
    @27
    @36
    @28
    @31
    @37
    syl2anc
    #
    cA
    @47
    @47
    eqid
    #
    ringmgp
    syl
    #
    ad3antrrr
    @24
    @41
    simpr
    #
    @24
    @2
    @41
    @0
    @1
    @2
    @21
    @23
    simpll3
    #
    adantr
    #
    cB
    c.ex
    @47
    @4
    cM
    cB
    cA
    @47
    @50
    chcoeffeq.b
    mgpbas
    #
    cayhamlem.e1
    mulgnn0cl
    syl3anc
    #
    @42
    cN
    cR
    ccpmat
    co
    #
    cB
    @7
    cU
    @3
    @57
    cB
    cU
    wf
    #
    @21
    @23
    @41
    @3
    @0
    @27
    @58
    @28
    @31
    cA
    cR
    @57
    cU
    cB
    cN
    chcoeffeq.a
    chcoeffeq.b
    @57
    eqid
    #
    chcoeffeq.u
    cpm2mf
    #
    syl2anc
    ad3antrrr
    @24
    cn0
    @57
    @4
    cG
    @24
    @0
    @27
    @2
    @21
    @23
    cn0
    @57
    cG
    wf
    #
    @29
    @32
    @53
    @3
    @21
    @23
    simplr
    @22
    @23
    simpr
    cA
    cB
    cP
    cR
    @57
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.t
    chcoeffeq.g
    @59
    chfacfisfcpmat
    syl32anc
    #
    ffvelrnda
    #
    ffvelrnd
    cB
    cA
    @9
    @5
    @8
    chcoeffeq.b
    @9
    eqid
    #
    ringcl
    #
    syl3anc
    @11
    eqid
    fmptd
    @24
    vz
    cvv
    @10
    vn
    cvv
    @33
    vw
    @24
    cA
    c0g
    fvexd
    @42
    @5
    @8
    @9
    ovexd
    @24
    cG
    cY
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vw
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    vn
    @69
    @10
    csb
    #
    @33
    wceq
    #
    wi
    #
    vz
    cn0
    wral
    #
    vw
    cn0
    wrex
    #
    @3
    @21
    @23
    @67
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.t
    chcoeffeq.g
    chfacffsupp
    anassrs
    @24
    @67
    @70
    @69
    cG
    cfv
    #
    @66
    wceq
    #
    wi
    #
    vz
    cn0
    wral
    #
    vw
    cn0
    wrex
    #
    @75
    @24
    cG
    @57
    cn0
    cmap
    co
    wcel
    #
    @66
    cvv
    wcel
    @67
    @80
    wi
    @24
    @81
    @61
    @62
    @57
    cvv
    wcel
    #
    @39
    wa
    @81
    @61
    wb
    @24
    @82
    @39
    cN
    cR
    ccpmat
    ovex
    nn0ex
    pm3.2i
    @57
    cn0
    cG
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    cY
    c0g
    fvex
    vz
    @57
    vw
    cG
    cvv
    @66
    fsuppmapnn0ub
    sylancl
    @24
    @79
    @74
    vw
    cn0
    @24
    @68
    cn0
    wcel
    #
    wa
    #
    @78
    @73
    vz
    cn0
    @84
    @69
    cn0
    wcel
    #
    wa
    @77
    @72
    @70
    @24
    @85
    @77
    @72
    wi
    @83
    @24
    @85
    wa
    #
    @77
    @72
    @86
    @77
    wa
    #
    @71
    @69
    cM
    c.ex
    co
    #
    @76
    cU
    cfv
    #
    @9
    co
    #
    @88
    @33
    @9
    co
    #
    @33
    @85
    @71
    @90
    wceq
    @24
    @77
    @85
    @71
    vn
    @69
    @5
    csb
    #
    vn
    @69
    @8
    csb
    #
    @9
    co
    @90
    vn
    @69
    @5
    @8
    @9
    cn0
    csbov12g
    @85
    @92
    @88
    @93
    @89
    @9
    @85
    @92
    vn
    @69
    @4
    csb
    #
    cM
    c.ex
    co
    @88
    vn
    @69
    @4
    cM
    c.ex
    cn0
    csbov1g
    @85
    @94
    @69
    cM
    c.ex
    vn
    @69
    cn0
    csbvarg
    oveq1d
    eqtrd
    @85
    @93
    vn
    @69
    @7
    csb
    #
    cU
    cfv
    @89
    vn
    @69
    @7
    cn0
    cU
    csbfv2g
    @85
    @95
    @76
    cU
    @95
    @76
    wceq
    @85
    vn
    @69
    cG
    csbfv
    a1i
    fveq2d
    eqtrd
    oveq12d
    eqtrd
    ad2antlr
    @87
    @89
    @33
    @88
    @9
    @77
    @86
    @89
    @66
    cU
    cfv
    #
    @33
    @76
    @66
    cU
    fveq2
    @22
    @96
    @33
    wceq
    #
    @23
    @85
    @22
    @0
    @27
    wa
    #
    @97
    @3
    @98
    @21
    @3
    @0
    @27
    @28
    @31
    jca
    adantr
    cA
    cY
    cP
    cR
    cU
    cN
    @33
    @66
    chcoeffeq.a
    chcoeffeq.u
    chcoeffeq.p
    chcoeffeq.y
    @34
    @66
    eqid
    m2cpminv0
    syl
    ad2antrr
    sylan9eqr
    oveq2d
    @87
    @36
    @88
    cB
    wcel
    #
    wa
    #
    @91
    @33
    wceq
    @86
    @100
    @77
    @86
    @36
    @99
    @24
    @36
    @85
    @46
    adantr
    @86
    @48
    @85
    @2
    @99
    @3
    @48
    @21
    @23
    @85
    @51
    ad3antrrr
    @24
    @85
    simpr
    @24
    @2
    @85
    @53
    adantr
    cB
    c.ex
    @47
    @69
    cM
    @55
    cayhamlem.e1
    mulgnn0cl
    syl3anc
    jca
    adantr
    cB
    cA
    @9
    @88
    @33
    chcoeffeq.b
    @64
    @34
    ringrz
    syl
    3eqtrd
    ex
    adantlr
    imim2d
    ralimdva
    reximdva
    syld
    mpd
    mptnn0fsupp
    #
    gsumcl
    cA
    cR
    cT
    cU
    cB
    @12
    cN
    chcoeffeq.u
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.t
    m2cpminvid
    syl3anc
    @24
    @25
    @17
    cU
    @24
    cY
    vn
    cn0
    @10
    cT
    cfv
    #
    cmpt
    #
    cgsu
    co
    @25
    @17
    @24
    vn
    cn0
    cB
    @10
    cA
    cY
    cT
    cvv
    @33
    chcoeffeq.b
    @34
    @38
    @3
    cY
    cmnd
    wcel
    #
    @21
    @23
    @3
    cY
    crg
    wcel
    #
    @104
    @3
    @0
    @27
    @105
    @28
    @31
    cY
    cP
    cR
    cN
    chcoeffeq.p
    chcoeffeq.y
    pmatring
    syl2anc
    cY
    ringmnd
    syl
    ad2antrr
    @40
    @24
    cT
    cA
    cY
    cghm
    co
    wcel
    #
    cT
    cA
    cY
    cmhm
    co
    wcel
    @24
    @0
    @27
    @106
    @29
    @32
    cA
    cB
    cY
    cP
    cR
    cT
    cW
    cN
    chcoeffeq.t
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.w
    mat2pmatghm
    syl2anc
    cA
    cY
    cT
    ghmmhm
    syl
    @42
    @36
    @43
    @44
    @45
    @3
    @36
    @21
    @23
    @41
    @49
    ad3antrrr
    @56
    @42
    @57
    cB
    @7
    cU
    @3
    @58
    @21
    @23
    @41
    @0
    @1
    @58
    @2
    @1
    @0
    @27
    @58
    @30
    @60
    sylan2
    3adant3
    ad3antrrr
    @63
    ffvelrnd
    #
    @65
    syl3anc
    @101
    gsummptmhm
    @24
    @103
    @16
    cY
    cgsu
    @24
    vn
    cn0
    @102
    @15
    @42
    @102
    @5
    cT
    cfv
    #
    @8
    cT
    cfv
    #
    c.xp
    co
    #
    @15
    @42
    cT
    cA
    cY
    crh
    co
    wcel
    #
    @43
    @44
    @102
    @110
    wceq
    @3
    @111
    @21
    @23
    @41
    @0
    @1
    @111
    @2
    cA
    cB
    cY
    cP
    cR
    cT
    cW
    cN
    chcoeffeq.t
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.w
    mat2pmatrhm
    3adant3
    ad3antrrr
    @56
    @107
    @5
    @8
    cA
    cY
    @9
    c.xp
    cT
    cB
    chcoeffeq.b
    @64
    chcoeffeq.r
    rhmmul
    syl3anc
    @42
    @108
    @14
    @109
    @7
    c.xp
    @42
    cT
    @47
    cY
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    @41
    @2
    @108
    @14
    wceq
    @3
    @113
    @21
    @23
    @41
    @0
    @1
    @113
    @2
    cA
    cB
    cY
    cP
    cR
    cT
    cW
    cN
    chcoeffeq.t
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.w
    mat2pmatmhm
    3adant3
    ad3antrrr
    @52
    @54
    cB
    c.ex
    cE
    cT
    @47
    @112
    @4
    cM
    @55
    cayhamlem.e1
    cayhamlem.e2
    mhmmulg
    syl3anc
    @42
    @0
    @27
    @7
    @57
    wcel
    @109
    @7
    wceq
    @3
    @0
    @21
    @23
    @41
    @28
    ad3antrrr
    @3
    @27
    @21
    @23
    @41
    @31
    ad3antrrr
    @63
    cR
    @57
    cT
    cU
    @7
    cN
    @59
    chcoeffeq.u
    chcoeffeq.t
    m2cpminvid2
    syl3anc
    oveq12d
    eqtrd
    mpteq2dva
    oveq2d
    eqtr3d
    fveq2d
    eqtr3d
    sylan9eqr
    cA
    cB
    cC
    cP
    cR
    cT
    @9
    c.xp
    cU
    c.1
    vn
    c.ex
    cG
    c.as
    cK
    cM
    c.mi
    cN
    cW
    cY
    c.0
    vs
    vb
    chcoeffeq.a
    chcoeffeq.b
    chcoeffeq.p
    chcoeffeq.y
    chcoeffeq.r
    chcoeffeq.s
    chcoeffeq.0
    chcoeffeq.t
    chcoeffeq.c
    chcoeffeq.k
    chcoeffeq.g
    chcoeffeq.w
    chcoeffeq.1
    chcoeffeq.m
    chcoeffeq.u
    cayhamlem.e1
    @64
    cayhamlem3
    reximddv2
end
