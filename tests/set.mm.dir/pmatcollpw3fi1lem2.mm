include "cc0.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfz.mm"
include "cn.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "wa.mm"
include "c1.mm"
include "c0g.mm"
include "cif.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "eqid.mm"
include "pmatcollpw3fi1lem1.mm"
include "syl3anc.mm"
include "1nn.mm"
include "a1i.mm"
include "wb.mm"
include "oveq2.mm"
include "mpteq1d.mm"
include "rexeqbidv.mm"
include "adantl.mm"
include "wf.mm"
include "wi.mm"
include "elmapi.mm"
include "c0ex.mm"
include "snid.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "ex.mm"
include "syl.mm"
include "imp.mm"
include "matring.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "fmptd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "adantr.mm"
include "rspcedv.mm"
include "rspcedvd.mm"
include "mpdan.mm"
include "rexlimdva.mm"
include "syl5bi.mm"

theorem pmatcollpw3fi1lem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cI: class I
  let vg: setvar g
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )
  assume pmatcollpw3.a: |- A = ( N Mat R )
  assume pmatcollpw3.d: |- D = ( Base ` A )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint B s
  disjoint n s
  disjoint C n
  disjoint M s
  disjoint N s
  disjoint R s
  disjoint B f
  disjoint C f
  disjoint f n
  disjoint D f
  disjoint M f
  disjoint N f
  disjoint R f
  disjoint T f
  disjoint X f
  disjoint .^ f
  disjoint .* f
  disjoint f s
  disjoint D n
  disjoint A f
  disjoint A n
  disjoint A s
  disjoint C s
  disjoint D s
  disjoint T s
  disjoint X s
  disjoint .^ s
  disjoint .* s
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i n
  disjoint j n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint .* a
  disjoint .* b
  disjoint .^ a
  disjoint .^ b
  disjoint .^ i
  disjoint .^ j
  disjoint f i
  disjoint f j
  disjoint B k
  disjoint B l
  disjoint B x
  disjoint B y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B m
  disjoint f x
  disjoint n x
  disjoint D k
  disjoint f k
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I x
  disjoint I y
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint I f
  disjoint I n
  disjoint k n
  disjoint M k
  disjoint M l
  disjoint M x
  disjoint M y
  disjoint M m
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint N k
  disjoint N l
  disjoint N x
  disjoint N y
  disjoint N m
  disjoint R k
  disjoint R l
  disjoint R x
  disjoint R y
  disjoint R m
  disjoint D l
  disjoint l n
  disjoint A l
  disjoint f l
  disjoint l s
  disjoint B g
  disjoint g l
  disjoint g n
  disjoint C g
  disjoint g s
  disjoint D g
  disjoint M g
  disjoint N g
  disjoint R g
  disjoint f g
  disjoint T g
  disjoint X g
  disjoint .^ g
  disjoint .* g
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( E. f e. ( D ^m { 0 } ) M = ( C gsum ( n e. { 0 } |-> ( ( n .^ X ) .* ( T ` ( f ` n ) ) ) ) ) -> E. s e. NN E. f e. ( D ^m ( 0 ... s ) ) M = ( C gsum ( n e. ( 0 ... s ) |-> ( ( n .^ X ) .* ( T ` ( f ` n ) ) ) ) ) ) )

  proof
    cM
    cC
    vn
    cc0
    csn
    #
    vn
    cv
    #
    cX
    c.ex
    co
    #
    @1
    vf
    cv
    #
    cfv
    #
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cD
    @0
    cmap
    co
    #
    wrex
    cM
    cC
    vn
    @0
    @2
    @1
    vg
    cv
    #
    cfv
    #
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vg
    @10
    wrex
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
    cM
    cC
    vn
    cc0
    vs
    cv
    #
    cfz
    co
    #
    @6
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cD
    @23
    cmap
    co
    #
    wrex
    #
    vs
    cn
    wrex
    #
    @9
    @17
    vf
    vg
    @10
    @3
    @11
    wceq
    #
    @8
    @16
    cM
    @30
    @7
    @15
    cC
    cgsu
    @30
    vn
    @0
    @6
    @14
    @30
    @5
    @13
    @2
    c.as
    @30
    @4
    @12
    cT
    @1
    @3
    @11
    fveq1
    fveq2d
    oveq2d
    mpteq2dv
    oveq2d
    eqeq2d
    cbvrexv
    @21
    @17
    @29
    vg
    @10
    @21
    @11
    @10
    wcel
    #
    wa
    #
    @17
    @29
    @32
    @17
    wa
    #
    cM
    cC
    vn
    cc0
    c1
    cfz
    co
    #
    @2
    @1
    vl
    @34
    vl
    cv
    #
    cc0
    wceq
    #
    cc0
    @11
    cfv
    #
    cA
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    #
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    @29
    @33
    @18
    cR
    crg
    wcel
    #
    wa
    #
    @31
    @17
    @46
    @21
    @48
    @31
    @17
    @18
    @19
    @48
    @20
    @19
    @47
    @18
    cR
    crngring
    #
    anim2i
    3adant3
    ad2antrr
    @21
    @31
    @17
    simplr
    @32
    @17
    simpr
    cA
    cB
    cC
    cD
    cP
    cR
    cT
    vn
    c.ex
    @11
    @40
    c.as
    cM
    cN
    cX
    @38
    vl
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpw3.a
    pmatcollpw3.d
    @38
    eqid
    #
    @40
    eqid
    #
    pmatcollpw3fi1lem1
    syl3anc
    @33
    @46
    wa
    #
    @28
    cM
    cC
    vn
    @34
    @6
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cD
    @34
    cmap
    co
    #
    wrex
    #
    vs
    c1
    cn
    c1
    cn
    wcel
    @52
    1nn
    a1i
    @22
    c1
    wceq
    #
    @28
    @57
    wb
    @52
    @58
    @26
    @55
    vf
    @27
    @56
    @58
    @23
    @34
    cD
    cmap
    @22
    c1
    cc0
    cfz
    oveq2
    #
    oveq2d
    @58
    @25
    @54
    cM
    @58
    @24
    @53
    cC
    cgsu
    @58
    vn
    @23
    @34
    @6
    @59
    mpteq1d
    oveq2d
    eqeq2d
    rexeqbidv
    adantl
    @33
    @46
    @57
    @33
    @55
    @46
    vf
    @40
    @56
    @32
    @40
    @56
    wcel
    #
    @17
    @32
    @60
    @34
    cD
    @40
    wf
    #
    @32
    vl
    @34
    @39
    cD
    @40
    @32
    @35
    @34
    wcel
    #
    wa
    @36
    @37
    @38
    cD
    @32
    @62
    @37
    cD
    wcel
    #
    @31
    @62
    @63
    wi
    #
    @21
    @31
    @0
    cD
    @11
    wf
    #
    @64
    @11
    cD
    @0
    elmapi
    @65
    @62
    @63
    @62
    @65
    cc0
    @0
    wcel
    #
    @63
    @66
    @62
    cc0
    c0ex
    snid
    a1i
    @0
    cD
    cc0
    @11
    ffvelrn
    sylan2
    ex
    syl
    adantl
    imp
    @21
    @38
    cD
    wcel
    #
    @31
    @62
    @21
    cA
    crg
    wcel
    #
    @67
    @18
    @19
    @68
    @20
    @19
    @18
    @47
    @68
    @49
    cA
    cR
    cN
    pmatcollpw3.a
    matring
    sylan2
    3adant3
    cD
    cA
    @38
    pmatcollpw3.d
    @50
    ring0cl
    syl
    ad2antrr
    ifcld
    @51
    fmptd
    cD
    cvv
    wcel
    #
    @34
    cvv
    wcel
    #
    wa
    @60
    @61
    wb
    @32
    @69
    @70
    cD
    cA
    cbs
    cfv
    cvv
    pmatcollpw3.d
    cA
    cbs
    fvex
    eqeltri
    cc0
    c1
    cfz
    ovex
    pm3.2i
    cD
    @34
    @40
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    adantr
    @3
    @40
    wceq
    #
    @55
    @46
    wb
    @33
    @71
    @54
    @45
    cM
    @71
    @53
    @44
    cC
    cgsu
    @71
    vn
    @34
    @6
    @43
    @71
    @5
    @42
    @2
    c.as
    @71
    @4
    @41
    cT
    @1
    @3
    @40
    fveq1
    fveq2d
    oveq2d
    mpteq2dv
    oveq2d
    eqeq2d
    adantl
    rspcedv
    imp
    rspcedvd
    mpdan
    ex
    rexlimdva
    syl5bi
end
