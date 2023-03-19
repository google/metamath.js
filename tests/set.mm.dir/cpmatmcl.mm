include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cco1.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cpmatmcllem.mm"
include "cbs.mm"
include "ply1ring.mm"
include "ad4antlr.mm"
include "eqid.mm"
include "cpmatpmat.mm"
include "3expa.mm"
include "anim12dan.mm"
include "adantr.mm"
include "simpr.mm"
include "anim1i.mm"
include "matmulcell.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidva.mm"
include "mpbird.mm"
include "wb.mm"
include "simpl.mm"
include "pmatring.mm"
include "w3a.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "syl.mm"
include "ringcl.mm"
include "cpmatel.mm"
include "ralrimivva.mm"

theorem cpmatmcl
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vl: setvar l
  assume cpmatsrngpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmatsrngpmat.p: |- P = ( Poly1 ` R )
  assume cpmatsrngpmat.c: |- C = ( N Mat P )

  disjoint N x
  disjoint N y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S y
  disjoint C i
  disjoint C j
  disjoint C n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint a y
  disjoint b i
  disjoint b j
  disjoint b x
  disjoint b y
  disjoint c i
  disjoint c j
  disjoint c x
  disjoint c y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint C k
  disjoint N k
  disjoint N l
  disjoint c k
  disjoint c l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint P k
  disjoint R k
  disjoint R l
  disjoint S c
  disjoint S i
  disjoint S j
  assert |- ( ( N e. Fin /\ R e. Ring ) -> A. x e. S A. y e. S ( x ( .r ` C ) y ) e. S )

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
    vy
    cv
    #
    cC
    cmulr
    cfv
    #
    co
    #
    cS
    wcel
    #
    vx
    vy
    cS
    cS
    @2
    @3
    cS
    wcel
    #
    @4
    cS
    wcel
    #
    wa
    #
    wa
    #
    @7
    vc
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    @6
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
    vc
    cn
    wral
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    @11
    @22
    @12
    cP
    vk
    cN
    @13
    vk
    cv
    #
    @3
    co
    @23
    @14
    @4
    co
    cP
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @18
    wceq
    #
    vc
    cn
    wral
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    vx
    vy
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    cN
    vc
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    cpmatmcllem
    @11
    @21
    @30
    vi
    cN
    @11
    @13
    cN
    wcel
    #
    wa
    #
    @20
    @29
    vj
    cN
    @32
    @14
    cN
    wcel
    #
    wa
    #
    @19
    @28
    vc
    cn
    @34
    @12
    cn
    wcel
    #
    wa
    #
    @17
    @27
    @18
    @36
    @12
    @16
    @26
    @34
    @16
    @26
    wceq
    @35
    @34
    @15
    @25
    cco1
    @34
    cP
    crg
    wcel
    #
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @4
    @38
    wcel
    #
    wa
    #
    @31
    @33
    wa
    @15
    @25
    wceq
    @1
    @37
    @0
    @10
    @31
    @33
    cP
    cR
    cpmatsrngpmat.p
    ply1ring
    ad4antlr
    @32
    @41
    @33
    @11
    @41
    @31
    @2
    @8
    @39
    @9
    @40
    @0
    @1
    @8
    @39
    @38
    cC
    cP
    cR
    cS
    @3
    cN
    crg
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @38
    eqid
    #
    cpmatpmat
    #
    3expa
    @0
    @1
    @9
    @40
    @38
    cC
    cP
    cR
    cS
    @4
    cN
    crg
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @42
    cpmatpmat
    #
    3expa
    anim12dan
    adantr
    adantr
    @32
    @31
    @33
    @11
    @31
    simpr
    anim1i
    cC
    @38
    cP
    @24
    @5
    vk
    @13
    @14
    cN
    @3
    @4
    cpmatsrngpmat.c
    @42
    @24
    eqid
    @5
    eqid
    #
    matmulcell
    syl3anc
    fveq2d
    adantr
    fveq1d
    eqeq1d
    ralbidva
    ralbidva
    ralbidva
    mpbird
    @11
    @0
    @1
    @6
    @38
    wcel
    #
    @7
    @22
    wb
    @2
    @0
    @10
    @0
    @1
    simpl
    adantr
    @2
    @1
    @10
    @0
    @1
    simpr
    adantr
    @11
    cC
    crg
    wcel
    #
    @39
    @40
    @46
    @2
    @47
    @10
    cC
    cP
    cR
    cN
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    pmatring
    adantr
    @11
    @0
    @1
    @8
    w3a
    #
    @39
    @11
    @2
    @8
    wa
    @48
    @10
    @8
    @2
    @8
    @9
    simpl
    anim2i
    @0
    @1
    @8
    df-3an
    sylibr
    @43
    syl
    @11
    @0
    @1
    @9
    w3a
    #
    @40
    @11
    @2
    @9
    wa
    @49
    @10
    @9
    @2
    @8
    @9
    simpr
    anim2i
    @0
    @1
    @9
    df-3an
    sylibr
    @44
    syl
    @38
    cC
    @5
    @3
    @4
    @42
    @45
    ringcl
    syl3anc
    @38
    cC
    cP
    cR
    cS
    vi
    vj
    vc
    @6
    cN
    crg
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @42
    cpmatel
    syl3anc
    mpbird
    ralrimivva
end
