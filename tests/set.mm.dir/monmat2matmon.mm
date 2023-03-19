include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cn0.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cdecpmat.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csb.mm"
include "crg.mm"
include "wceq.mm"
include "crngring.mm"
include "simpll.mm"
include "simplr.mm"
include "mat2pmatscmxcl.mm"
include "pm2mpfval.mm"
include "syl3anc.mm"
include "sylanl2.mm"
include "c0g.mm"
include "cif.mm"
include "w3a.mm"
include "simpr.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eqid.mm"
include "monmatcollpw.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "wi.mm"
include "a1i.mm"
include "anim2d.mm"
include "anim1d.mm"
include "imdistanri.mm"
include "ovif.mm"
include "csca.mm"
include "matring.mm"
include "ply1sca.mm"
include "syl.mm"
include "ad2antrr.mm"
include "fveq2d.mm"
include "clmod.mm"
include "cbs.mm"
include "ply1lmod.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "lmod0vs.mm"
include "eqtrd.mm"
include "ifeq2d.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cvv.mm"
include "ringmnd.mm"
include "adantr.mm"
include "nn0ex.mm"
include "simprr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "lmodvscl.mm"
include "ralrimiva.mm"
include "gsummpt1n0.mm"
include "csbov2g.mm"
include "csbov1g.mm"
include "csbvarg.mm"
include "ad2antll.mm"
include "3eqtrd.mm"

theorem monmat2matmon
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cE: class E
  let c.ex: class .^
  let cI: class I
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
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


  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. K /\ L e. NN0 ) ) -> ( I ` ( ( L E Y ) .x. ( T ` M ) ) ) = ( M .* ( L .^ X ) ) )

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
    wcel
    #
    cL
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cL
    cY
    cE
    co
    cM
    cT
    cfv
    c.x
    co
    #
    cI
    cfv
    #
    cQ
    vk
    cn0
    @7
    vk
    cv
    #
    cdecpmat
    co
    #
    @9
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    vk
    cL
    cM
    @11
    c.as
    co
    #
    csb
    #
    cM
    cL
    cX
    c.ex
    co
    #
    c.as
    co
    #
    @1
    @0
    cR
    crg
    wcel
    #
    @5
    @8
    @14
    wceq
    #
    cR
    crngring
    #
    @0
    @19
    wa
    #
    @5
    wa
    #
    @0
    @19
    @7
    cB
    wcel
    @20
    @0
    @19
    @5
    simpll
    @0
    @19
    @5
    simplr
    cA
    cB
    cC
    cP
    cR
    cT
    cE
    c.x
    cK
    cL
    cM
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
    cA
    cB
    cC
    cP
    cQ
    cR
    cI
    vk
    c.ex
    c.as
    @7
    cN
    crg
    cX
    monmat2matmon.p
    monmat2matmon.c
    monmat2matmon.b
    monmat2matmon.m1
    monmat2matmon.e1
    monmat2matmon.x
    monmat2matmon.a
    monmat2matmon.q
    monmat2matmon.i
    pm2mpfval
    syl3anc
    sylanl2
    @6
    @14
    cQ
    vk
    cn0
    @9
    cL
    wceq
    #
    @15
    cQ
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cgsu
    co
    #
    @16
    @6
    @13
    @27
    cQ
    cgsu
    @6
    vk
    cn0
    @12
    @26
    @6
    @9
    cn0
    wcel
    #
    wa
    #
    @12
    @24
    cM
    cA
    c0g
    cfv
    #
    cif
    #
    @11
    c.as
    co
    #
    @26
    @30
    @10
    @32
    @11
    c.as
    @30
    @2
    @3
    @4
    @29
    w3a
    #
    @10
    @32
    wceq
    @2
    @5
    @29
    simpll
    @30
    @5
    @29
    wa
    @34
    @6
    @5
    @29
    @2
    @5
    simpr
    anim1i
    @3
    @4
    @29
    df-3an
    sylibr
    cA
    cC
    cP
    cR
    cT
    c.x
    cE
    @9
    cK
    cL
    cM
    cN
    cY
    @31
    monmat2matmon.p
    monmat2matmon.c
    monmat2matmon.a
    monmat2matmon.k
    @31
    eqid
    monmat2matmon.e2
    monmat2matmon.y
    monmat2matmon.m2
    monmat2matmon.t
    monmatcollpw
    syl2anc
    oveq1d
    @30
    @23
    @29
    wa
    #
    @33
    @26
    wceq
    @29
    @6
    @23
    @29
    @2
    @22
    @5
    @29
    @1
    @19
    @0
    @1
    @19
    wi
    @29
    @21
    a1i
    anim2d
    anim1d
    imdistanri
    @35
    @33
    @24
    @15
    @31
    @11
    c.as
    co
    #
    cif
    @26
    @24
    cM
    @31
    @11
    c.as
    ovif
    @35
    @24
    @36
    @25
    @15
    @35
    @36
    cQ
    csca
    cfv
    #
    c0g
    cfv
    #
    @11
    c.as
    co
    #
    @25
    @35
    @31
    @38
    @11
    c.as
    @35
    cA
    @37
    c0g
    @22
    cA
    @37
    wceq
    #
    @5
    @29
    @22
    cA
    crg
    wcel
    #
    @40
    cA
    cR
    cN
    monmat2matmon.a
    matring
    #
    cQ
    cA
    crg
    monmat2matmon.q
    ply1sca
    syl
    #
    ad2antrr
    fveq2d
    oveq1d
    @35
    cQ
    clmod
    wcel
    #
    @11
    cQ
    cbs
    cfv
    #
    wcel
    #
    @39
    @25
    wceq
    @22
    @44
    @5
    @29
    @22
    @41
    @44
    @42
    cQ
    cA
    monmat2matmon.q
    ply1lmod
    syl
    ad2antrr
    #
    @35
    cQ
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @29
    cX
    @45
    wcel
    #
    @46
    @22
    @49
    @5
    @29
    @22
    cQ
    crg
    wcel
    #
    @49
    @22
    @41
    @51
    @42
    cQ
    cA
    monmat2matmon.q
    ply1ring
    syl
    #
    cQ
    @48
    @48
    eqid
    #
    ringmgp
    syl
    ad2antrr
    @23
    @29
    simpr
    @22
    @50
    @5
    @29
    @22
    @41
    @50
    @42
    @45
    cQ
    cA
    cX
    monmat2matmon.x
    monmat2matmon.q
    @45
    eqid
    #
    vr1cl
    syl
    ad2antrr
    @45
    c.ex
    @48
    @9
    cX
    @45
    cQ
    @48
    @53
    @54
    mgpbas
    monmat2matmon.e1
    mulgnn0cl
    syl3anc
    #
    c.as
    @37
    @38
    @45
    cQ
    @11
    @25
    @54
    @37
    eqid
    #
    monmat2matmon.m1
    @38
    eqid
    @25
    eqid
    #
    lmod0vs
    syl2anc
    eqtrd
    ifeq2d
    syl5eq
    syl
    eqtrd
    mpteq2dva
    oveq2d
    @1
    @0
    @19
    @5
    @28
    @16
    wceq
    @21
    @23
    @15
    vk
    @27
    cQ
    cn0
    cvv
    cL
    @25
    @57
    @22
    cQ
    cmnd
    wcel
    #
    @5
    @22
    @51
    @58
    @52
    cQ
    ringmnd
    syl
    adantr
    cn0
    cvv
    wcel
    @23
    nn0ex
    a1i
    @22
    @3
    @4
    simprr
    @27
    eqid
    @23
    @15
    @45
    wcel
    #
    vk
    cn0
    @35
    @44
    cM
    @37
    cbs
    cfv
    #
    wcel
    #
    @46
    @59
    @47
    @23
    @61
    @29
    @5
    @22
    @61
    @3
    @22
    @61
    wi
    @4
    @22
    @3
    @61
    @22
    cK
    @60
    cM
    @22
    cK
    cA
    cbs
    cfv
    @60
    monmat2matmon.k
    @22
    cA
    @37
    cbs
    @43
    fveq2d
    syl5eq
    eleq2d
    biimpcd
    adantr
    impcom
    adantr
    @55
    cM
    c.as
    @37
    @60
    @45
    cQ
    @11
    @54
    @56
    monmat2matmon.m1
    @60
    eqid
    lmodvscl
    syl3anc
    ralrimiva
    gsummpt1n0
    sylanl2
    eqtrd
    @4
    @16
    @18
    wceq
    @2
    @3
    @4
    @16
    cM
    vk
    cL
    @11
    csb
    #
    c.as
    co
    @18
    vk
    cL
    cM
    @11
    c.as
    cn0
    csbov2g
    @4
    @62
    @17
    cM
    c.as
    @4
    @62
    vk
    cL
    @9
    csb
    #
    cX
    c.ex
    co
    @17
    vk
    cL
    @9
    cX
    c.ex
    cn0
    csbov1g
    @4
    @63
    cL
    cX
    c.ex
    vk
    cL
    cn0
    csbvarg
    oveq1d
    eqtrd
    oveq2d
    eqtrd
    ad2antll
    3eqtrd
end
