include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cvv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cdecpmat.mm"
include "cmin.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c0g.mm"
include "fvexd.mm"
include "cn0.mm"
include "ovexd.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cco1.mm"
include "cmpt2.mm"
include "simpll.mm"
include "simplr.mm"
include "w3a.mm"
include "pmatring.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "eqid.mm"
include "ringcl.mm"
include "syl.mm"
include "pmatcoe1fsupp.mm"
include "syl3anc.mm"
include "csca.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "rspc2va.mm"
include "expcom.mm"
include "adantl.mm"
include "3impib.mm"
include "mpt2eq3dva.mm"
include "mat0op.mm"
include "ad3antrrr.mm"
include "matring.mm"
include "ply1sca.mm"
include "3eqtr2d.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "adantr.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "decpmatval.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "simpllr.mm"
include "simpr.mm"
include "decpmatmul.mm"
include "eqcomd.mm"
include "mptnn0fsuppd.mm"

theorem pm2mpmhmlem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cL: class L
  let cN: class N
  let cX: class X
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vs: setvar s
  assume pm2mpfo.p: |- P = ( Poly1 ` R )
  assume pm2mpfo.c: |- C = ( N Mat P )
  assume pm2mpfo.b: |- B = ( Base ` C )
  assume pm2mpfo.m: |- .* = ( .s ` Q )
  assume pm2mpfo.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpfo.x: |- X = ( var1 ` A )
  assume pm2mpfo.a: |- A = ( N Mat R )
  assume pm2mpfo.q: |- Q = ( Poly1 ` A )
  assume pm2mpfo.l: |- L = ( Base ` Q )
  assume pm2mpfo.t: |- T = ( N pMatToMatPoly R )

  disjoint A k
  disjoint B k
  disjoint B l
  disjoint k l
  disjoint C k
  disjoint C l
  disjoint L k
  disjoint N k
  disjoint N l
  disjoint Q k
  disjoint R k
  disjoint .* k
  disjoint A l
  disjoint P k
  disjoint R l
  disjoint X l
  disjoint .* l
  disjoint .^ l
  disjoint x y
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint B a
  disjoint B b
  disjoint B i
  disjoint B j
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint a l
  disjoint i l
  disjoint j l
  disjoint B n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint l n
  disjoint C a
  disjoint C b
  disjoint C i
  disjoint C j
  disjoint C n
  disjoint L a
  disjoint L b
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint Q a
  disjoint Q b
  disjoint R a
  disjoint R b
  disjoint R i
  disjoint R j
  disjoint T a
  disjoint T b
  disjoint A n
  disjoint A s
  disjoint l s
  disjoint n s
  disjoint B s
  disjoint C s
  disjoint N s
  disjoint Q n
  disjoint Q s
  disjoint R n
  disjoint R s
  disjoint X n
  disjoint X s
  disjoint .* n
  disjoint .* s
  disjoint .^ n
  disjoint .^ s
  disjoint a s
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint b s
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint s x
  disjoint s y
  disjoint n x
  disjoint n y
  disjoint k s
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( x e. B /\ y e. B ) ) -> ( l e. NN0 |-> ( ( A gsum ( k e. ( 0 ... l ) |-> ( ( x decompPMat k ) ( .r ` A ) ( y decompPMat ( l - k ) ) ) ) ) .* ( l .^ X ) ) ) finSupp ( 0g ` Q ) )

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
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    vn
    cvv
    cA
    vk
    cc0
    vl
    cv
    #
    cfz
    co
    #
    @3
    vk
    cv
    #
    cdecpmat
    co
    #
    @5
    @9
    @11
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
    @9
    cX
    c.ex
    co
    #
    c.as
    co
    cA
    vk
    cc0
    vn
    cv
    #
    cfz
    co
    #
    @12
    @5
    @20
    @11
    cmin
    co
    #
    cdecpmat
    co
    #
    @15
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @20
    cX
    c.ex
    co
    #
    c.as
    co
    #
    vl
    cvv
    cQ
    c0g
    cfv
    #
    vs
    @8
    cQ
    c0g
    fvexd
    @8
    @9
    cn0
    wcel
    wa
    @18
    @19
    c.as
    ovexd
    @9
    @20
    wceq
    #
    @18
    @26
    @19
    @27
    c.as
    @30
    @17
    @25
    cA
    cgsu
    @30
    vk
    @10
    @16
    @21
    @24
    @9
    @20
    cc0
    cfz
    oveq2
    @30
    @14
    @23
    @12
    @15
    @30
    @13
    @22
    @5
    cdecpmat
    @9
    @20
    @11
    cmin
    oveq1
    oveq2d
    oveq2d
    mpteq12dv
    oveq2d
    @9
    @20
    cX
    c.ex
    oveq1
    oveq12d
    @8
    vs
    cv
    @20
    clt
    wbr
    #
    @28
    @29
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    @31
    @3
    @5
    cC
    cmulr
    cfv
    #
    co
    #
    @20
    cdecpmat
    co
    #
    @27
    c.as
    co
    #
    @29
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @8
    @42
    @31
    vi
    vj
    cN
    cN
    @20
    vi
    cv
    #
    vj
    cv
    #
    @36
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    @27
    c.as
    co
    #
    @29
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @8
    @31
    @20
    va
    cv
    #
    vb
    cv
    #
    @36
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @53
    @8
    @0
    @1
    @36
    cB
    wcel
    #
    @64
    @0
    @1
    @7
    simpll
    @0
    @1
    @7
    simplr
    @8
    cC
    crg
    wcel
    #
    @4
    @6
    w3a
    #
    @65
    @8
    @66
    @7
    wa
    @67
    @2
    @66
    @7
    cC
    cP
    cR
    cN
    pm2mpfo.p
    pm2mpfo.c
    pmatring
    anim1i
    @66
    @4
    @6
    3anass
    sylibr
    cB
    cC
    @35
    @3
    @5
    pm2mpfo.b
    @35
    eqid
    ringcl
    syl
    #
    vn
    cB
    cC
    cP
    cR
    va
    vb
    @36
    cN
    @59
    vs
    pm2mpfo.p
    pm2mpfo.c
    pm2mpfo.b
    @59
    eqid
    #
    pmatcoe1fsupp
    syl3anc
    @8
    @63
    @52
    vs
    cn0
    @8
    @62
    @51
    vn
    cn0
    @8
    @20
    cn0
    wcel
    #
    wa
    #
    @61
    @50
    @31
    @71
    @61
    @50
    @71
    @61
    wa
    #
    @49
    cQ
    csca
    cfv
    #
    c0g
    cfv
    #
    @27
    c.as
    co
    #
    @29
    @72
    @48
    @74
    @27
    c.as
    @72
    @48
    vi
    vj
    cN
    cN
    @59
    cmpt2
    #
    cA
    c0g
    cfv
    #
    @74
    @72
    vi
    vj
    cN
    cN
    @47
    @59
    @72
    @43
    cN
    wcel
    #
    @44
    cN
    wcel
    #
    @47
    @59
    wceq
    #
    @61
    @78
    @79
    wa
    #
    @80
    wi
    @71
    @81
    @61
    @80
    @60
    @80
    @20
    @43
    @55
    @36
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @59
    wceq
    va
    vb
    @43
    @44
    cN
    cN
    @54
    @43
    wceq
    #
    @58
    @84
    @59
    @85
    @20
    @57
    @83
    @85
    @56
    @82
    cco1
    @54
    @43
    @55
    @36
    oveq1
    fveq2d
    fveq1d
    eqeq1d
    @55
    @44
    wceq
    #
    @84
    @47
    @59
    @86
    @20
    @83
    @46
    @86
    @82
    @45
    cco1
    @55
    @44
    @43
    @36
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    rspc2va
    expcom
    adantl
    3impib
    mpt2eq3dva
    @2
    @77
    @76
    wceq
    @7
    @70
    @61
    cA
    cR
    vi
    vj
    cN
    @59
    pm2mpfo.a
    @69
    mat0op
    ad3antrrr
    @72
    cA
    @73
    c0g
    @2
    cA
    @73
    wceq
    #
    @7
    @70
    @61
    @2
    cA
    crg
    wcel
    #
    @87
    cA
    cR
    cN
    pm2mpfo.a
    matring
    #
    cQ
    cA
    crg
    pm2mpfo.q
    ply1sca
    syl
    ad3antrrr
    fveq2d
    3eqtr2d
    oveq1d
    @71
    @75
    @29
    wceq
    #
    @61
    @71
    cQ
    clmod
    wcel
    #
    @27
    cL
    wcel
    #
    @90
    @8
    @91
    @70
    @2
    @91
    @7
    @2
    @88
    @91
    @89
    cQ
    cA
    pm2mpfo.q
    ply1lmod
    syl
    adantr
    adantr
    @8
    @88
    @70
    @92
    @2
    @88
    @7
    @89
    adantr
    cL
    @20
    cQ
    cA
    c.ex
    cQ
    cmgp
    cfv
    #
    cX
    pm2mpfo.q
    pm2mpfo.x
    @93
    eqid
    pm2mpfo.e
    pm2mpfo.l
    ply1moncl
    sylan
    c.as
    @73
    @74
    cL
    cQ
    @27
    @29
    pm2mpfo.l
    @73
    eqid
    pm2mpfo.m
    @74
    eqid
    @29
    eqid
    lmod0vs
    syl2anc
    adantr
    eqtrd
    ex
    imim2d
    ralimdva
    reximdv
    mpd
    @8
    @41
    @52
    vs
    cn0
    @8
    @40
    @51
    vn
    cn0
    @71
    @39
    @50
    @31
    @71
    @38
    @49
    @29
    @71
    @37
    @48
    @27
    c.as
    @8
    @65
    @70
    @37
    @48
    wceq
    @68
    cC
    cB
    cP
    vi
    vj
    @20
    @36
    cN
    pm2mpfo.c
    pm2mpfo.b
    decpmatval
    sylan
    oveq1d
    eqeq1d
    imbi2d
    ralbidva
    rexbidv
    mpbird
    @8
    @34
    @41
    vs
    cn0
    @8
    @33
    @40
    vn
    cn0
    @71
    @32
    @39
    @31
    @71
    @28
    @38
    @29
    @71
    @26
    @37
    @27
    c.as
    @71
    @37
    @26
    @71
    @1
    @7
    @70
    @37
    @26
    wceq
    @0
    @1
    @7
    @70
    simpllr
    @2
    @7
    @70
    simplr
    @8
    @70
    simpr
    cA
    cB
    cC
    cP
    cR
    @3
    vk
    @20
    cN
    @5
    pm2mpfo.p
    pm2mpfo.c
    pm2mpfo.b
    pm2mpfo.a
    decpmatmul
    syl3anc
    eqcomd
    oveq1d
    eqeq1d
    imbi2d
    ralbidva
    rexbidv
    mpbird
    mptnn0fsuppd
end
