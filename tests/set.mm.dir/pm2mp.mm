include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "pmatring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "adantr.mm"
include "cmnd.mm"
include "matring.mm"
include "sylan2.mm"
include "ply1ring.mm"
include "ringmnd.mm"
include "nn0ex.mm"
include "a1i.mm"
include "cghm.mm"
include "cmhm.mm"
include "cbs.mm"
include "pm2mpghm.mm"
include "ghmmhm.mm"
include "syl.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "mat2pmatscmxcl.mm"
include "syl12anc.mm"
include "fvexd.mm"
include "ovexd.mm"
include "clt.mm"
include "csb.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "fvex.mm"
include "fsuppmapnn0ub.mm"
include "sylancl.mm"
include "csbov12g.mm"
include "csbov1g.mm"
include "csbvarg.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "csbfv2g.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "mat2pmatghm.mm"
include "ad3antrrr.mm"
include "mhm0.mm"
include "clmod.mm"
include "csca.mm"
include "matlmod.mm"
include "cmgp.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "ply1crng.mm"
include "matsca2.mm"
include "eqcomd.mm"
include "eleqtrrd.mm"
include "lmodvs0.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "syld.mm"
include "impr.mm"
include "mptnn0fsupp.mm"
include "gsummptmhm.mm"
include "simpll.mm"
include "monmat2matmon.mm"
include "mpteq2dva.mm"
include "eqtr3d.mm"

theorem pm2mp
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cI: class I
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume monmat2matmon.p: |- P = ( Poly1 ` R )
  assume monmat2matmon.c: |- C = ( N Mat P )
  assume monmat2matmon.b: |- B = ( Base ` C )
  assume monmat2matmon.m1: |- .* = ( .s ` Q )
  assume monmat2matmon.e1: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume monmat2matmon.x: |- X = ( var1 ` A )
  assume monmat2matmon.a: |- A = ( N Mat R )
  assume monmat2matmon.k: |- K = ( Base ` A )
  assume monmat2matmon.q: |- Q = ( Poly1 ` A )
  assume monmat2matmon.i: |- I = ( N pMatToMatPoly R )
  assume monmat2matmon.e2: |- E = ( .g ` ( mulGrp ` P ) )
  assume monmat2matmon.y: |- Y = ( var1 ` R )
  assume monmat2matmon.m2: |- .x. = ( .s ` C )
  assume monmat2matmon.t: |- T = ( N matToPolyMat R )

  disjoint A n
  disjoint B n
  disjoint E n
  disjoint I n
  disjoint K n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint T n
  disjoint Y n
  disjoint .x. n
  disjoint B k
  disjoint E k
  disjoint K k
  disjoint L k
  disjoint M k
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint x y
  disjoint Q k
  disjoint R k
  disjoint T k
  disjoint X k
  disjoint Y k
  disjoint .* k
  disjoint .^ k
  disjoint .x. k
  disjoint A x
  disjoint A y
  disjoint n x
  disjoint n y
  disjoint C x
  disjoint C y
  disjoint E x
  disjoint E y
  disjoint K x
  disjoint K y
  disjoint M x
  disjoint M y
  disjoint R x
  disjoint R y
  disjoint T x
  disjoint T y
  disjoint Y x
  disjoint Y y
  disjoint .x. x
  disjoint .x. y
  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. ( K ^m NN0 ) /\ M finSupp ( 0g ` A ) ) ) -> ( I ` ( C gsum ( n e. NN0 |-> ( ( n E Y ) .x. ( T ` ( M ` n ) ) ) ) ) ) = ( Q gsum ( n e. NN0 |-> ( ( M ` n ) .* ( n .^ X ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cM
    cK
    cn0
    cmap
    co
    wcel
    #
    cM
    cA
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    wa
    #
    wa
    #
    cQ
    vn
    cn0
    vn
    cv
    #
    cY
    cE
    co
    #
    @8
    cM
    cfv
    #
    cT
    cfv
    #
    c.x
    co
    #
    cI
    cfv
    #
    cmpt
    #
    cgsu
    co
    cC
    vn
    cn0
    @12
    cmpt
    cgsu
    co
    cI
    cfv
    cQ
    vn
    cn0
    @10
    @8
    cX
    c.ex
    co
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    @7
    vn
    cn0
    cB
    @12
    cC
    cQ
    cI
    cvv
    cC
    c0g
    cfv
    #
    monmat2matmon.b
    @17
    eqid
    #
    @2
    cC
    ccmn
    wcel
    #
    @6
    @2
    @0
    cR
    crg
    wcel
    #
    wa
    #
    cC
    crg
    wcel
    @19
    @1
    @20
    @0
    cR
    crngring
    #
    anim2i
    #
    cC
    cP
    cR
    cN
    monmat2matmon.p
    monmat2matmon.c
    pmatring
    cC
    ringcmn
    3syl
    adantr
    @2
    cQ
    cmnd
    wcel
    #
    @6
    @2
    cA
    crg
    wcel
    #
    cQ
    crg
    wcel
    @24
    @1
    @0
    @20
    @25
    @22
    cA
    cR
    cN
    monmat2matmon.a
    matring
    sylan2
    cQ
    cA
    monmat2matmon.q
    ply1ring
    cQ
    ringmnd
    3syl
    adantr
    cn0
    cvv
    wcel
    @7
    nn0ex
    a1i
    @7
    cI
    cC
    cQ
    cghm
    co
    wcel
    #
    cI
    cC
    cQ
    cmhm
    co
    wcel
    @2
    @26
    @6
    @1
    @0
    @20
    @26
    @22
    cA
    cB
    cC
    cP
    cQ
    cR
    cI
    c.ex
    c.as
    cQ
    cbs
    cfv
    #
    cN
    cX
    monmat2matmon.p
    monmat2matmon.c
    monmat2matmon.b
    monmat2matmon.m1
    monmat2matmon.e1
    monmat2matmon.x
    monmat2matmon.a
    monmat2matmon.q
    @27
    eqid
    monmat2matmon.i
    pm2mpghm
    sylan2
    adantr
    cC
    cQ
    cI
    ghmmhm
    syl
    @7
    @8
    cn0
    wcel
    #
    wa
    #
    @21
    @10
    cK
    wcel
    #
    @28
    @12
    cB
    wcel
    @7
    @21
    @28
    @2
    @21
    @6
    @23
    adantr
    adantr
    @7
    cn0
    cK
    @8
    cM
    @6
    cn0
    cK
    cM
    wf
    #
    @2
    @3
    @31
    @5
    cM
    cK
    cn0
    elmapi
    adantr
    adantl
    ffvelrnda
    #
    @7
    @28
    simpr
    #
    cA
    cB
    cC
    cP
    cR
    cT
    cE
    c.x
    cK
    @8
    @10
    cN
    cY
    monmat2matmon.a
    monmat2matmon.k
    monmat2matmon.t
    monmat2matmon.p
    monmat2matmon.c
    monmat2matmon.b
    monmat2matmon.m2
    monmat2matmon.e2
    monmat2matmon.y
    mat2pmatscmxcl
    syl12anc
    @7
    vx
    cvv
    @12
    vn
    cvv
    @17
    vy
    @7
    cC
    c0g
    fvexd
    @29
    @9
    @11
    c.x
    ovexd
    @2
    @3
    @5
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vn
    @35
    @12
    csb
    #
    @17
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @2
    @3
    wa
    #
    @5
    @36
    @35
    cM
    cfv
    #
    @4
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    cn0
    wrex
    #
    @41
    @42
    @3
    @4
    cvv
    wcel
    @5
    @47
    wi
    @2
    @3
    simpr
    cA
    c0g
    fvex
    vx
    cK
    vy
    cM
    cvv
    @4
    fsuppmapnn0ub
    sylancl
    @42
    @46
    @40
    vy
    cn0
    @42
    @34
    cn0
    wcel
    #
    wa
    #
    @45
    @39
    vx
    cn0
    @49
    @35
    cn0
    wcel
    #
    wa
    #
    @44
    @38
    @36
    @51
    @44
    @38
    @51
    @44
    wa
    @37
    @35
    cY
    cE
    co
    #
    @43
    cT
    cfv
    #
    c.x
    co
    #
    @17
    @51
    @37
    @54
    wceq
    #
    @44
    @50
    @55
    @49
    @50
    @37
    vn
    @35
    @9
    csb
    #
    vn
    @35
    @11
    csb
    #
    c.x
    co
    @54
    vn
    @35
    @9
    @11
    c.x
    cn0
    csbov12g
    @50
    @56
    @52
    @57
    @53
    c.x
    @50
    @56
    vn
    @35
    @8
    csb
    #
    cY
    cE
    co
    @52
    vn
    @35
    @8
    cY
    cE
    cn0
    csbov1g
    @50
    @58
    @35
    cY
    cE
    vn
    @35
    cn0
    csbvarg
    #
    oveq1d
    eqtrd
    @50
    @57
    vn
    @35
    @10
    csb
    #
    cT
    cfv
    @53
    vn
    @35
    @10
    cn0
    cT
    csbfv2g
    @50
    @60
    @43
    cT
    @50
    @60
    @58
    cM
    cfv
    @43
    vn
    @35
    @8
    cn0
    cM
    csbfv2g
    @50
    @58
    @35
    cM
    @59
    fveq2d
    eqtrd
    fveq2d
    eqtrd
    oveq12d
    eqtrd
    adantl
    adantr
    @44
    @51
    @54
    @52
    @4
    cT
    cfv
    #
    c.x
    co
    #
    @17
    @44
    @53
    @61
    @52
    c.x
    @43
    @4
    cT
    fveq2
    oveq2d
    @51
    @62
    @52
    @17
    c.x
    co
    #
    @17
    @51
    @61
    @17
    @52
    c.x
    @51
    cT
    cA
    cC
    cghm
    co
    wcel
    #
    cT
    cA
    cC
    cmhm
    co
    wcel
    @61
    @17
    wceq
    @2
    @64
    @3
    @48
    @50
    @1
    @0
    @20
    @64
    @22
    cA
    cK
    cC
    cP
    cR
    cT
    cB
    cN
    monmat2matmon.t
    monmat2matmon.a
    monmat2matmon.k
    monmat2matmon.p
    monmat2matmon.c
    monmat2matmon.b
    mat2pmatghm
    sylan2
    ad3antrrr
    cA
    cC
    cT
    ghmmhm
    cA
    cC
    cT
    @17
    @4
    @4
    eqid
    @18
    mhm0
    3syl
    oveq2d
    @51
    cC
    clmod
    wcel
    #
    @52
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @63
    @17
    wceq
    @2
    @65
    @3
    @48
    @50
    @1
    @0
    cP
    crg
    wcel
    #
    @65
    @1
    @20
    @68
    @22
    cP
    cR
    monmat2matmon.p
    ply1ring
    syl
    #
    cC
    cP
    cN
    monmat2matmon.c
    matlmod
    sylan2
    ad3antrrr
    @51
    @52
    cP
    cbs
    cfv
    #
    @67
    @51
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @50
    cY
    @70
    wcel
    #
    @52
    @70
    wcel
    @2
    @72
    @3
    @48
    @50
    @2
    @68
    @72
    @1
    @68
    @0
    @69
    adantl
    cP
    @71
    @71
    eqid
    #
    ringmgp
    syl
    ad3antrrr
    @49
    @50
    simpr
    @2
    @73
    @3
    @48
    @50
    @2
    @20
    @73
    @1
    @20
    @0
    @22
    adantl
    @70
    cP
    cR
    cY
    monmat2matmon.y
    monmat2matmon.p
    @70
    eqid
    #
    vr1cl
    syl
    ad3antrrr
    @70
    cE
    @71
    @35
    cY
    @70
    cP
    @71
    @74
    @75
    mgpbas
    monmat2matmon.e2
    mulgnn0cl
    syl3anc
    @51
    @66
    cP
    cbs
    @2
    @66
    cP
    wceq
    @3
    @48
    @50
    @2
    cP
    @66
    @1
    @0
    cP
    ccrg
    wcel
    cP
    @66
    wceq
    cP
    cR
    monmat2matmon.p
    ply1crng
    cC
    cP
    cN
    ccrg
    monmat2matmon.c
    matsca2
    sylan2
    eqcomd
    ad3antrrr
    fveq2d
    eleqtrrd
    c.x
    @66
    @67
    cC
    @52
    @17
    @66
    eqid
    monmat2matmon.m2
    @67
    eqid
    @18
    lmodvs0
    syl2anc
    eqtrd
    sylan9eqr
    eqtrd
    ex
    imim2d
    ralimdva
    reximdva
    syld
    impr
    mptnn0fsupp
    gsummptmhm
    @7
    @14
    @16
    cQ
    cgsu
    @7
    vn
    cn0
    @13
    @15
    @29
    @2
    @30
    @28
    @13
    @15
    wceq
    @2
    @6
    @28
    simpll
    @32
    @33
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    c.x
    cE
    c.ex
    cI
    c.as
    cK
    @8
    @10
    cN
    cX
    cY
    monmat2matmon.p
    monmat2matmon.c
    monmat2matmon.b
    monmat2matmon.m1
    monmat2matmon.e1
    monmat2matmon.x
    monmat2matmon.a
    monmat2matmon.k
    monmat2matmon.q
    monmat2matmon.i
    monmat2matmon.e2
    monmat2matmon.y
    monmat2matmon.m2
    monmat2matmon.t
    monmat2matmon
    syl12anc
    mpteq2dva
    oveq2d
    eqtr3d
end
