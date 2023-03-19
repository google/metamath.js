include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cascl.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "eqid.mm"
include "cpmatelimp2.mm"
include "r19.26-2.mm"
include "csca.mm"
include "ringacl.mm"
include "3expb.mm"
include "wb.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "eleq1d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "ad3antlr.mm"
include "imp.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "simpr.mm"
include "ancomd.mm"
include "anim1i.mm"
include "ad2antrr.mm"
include "matplusgcell.mm"
include "syl.mm"
include "oveq12.mm"
include "ancoms.mm"
include "cghm.mm"
include "ply1ring.mm"
include "ad4antlr.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclghm.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "adantrd.mm"
include "adantld.mm"
include "ghmlin.mm"
include "syl3anc.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "expd.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "com23.mm"
include "impd.mm"
include "ralimdvva.mm"
include "syl5bir.mm"
include "expr.mm"
include "com34.mm"
include "syld.mm"
include "imp32.mm"
include "simpl.mm"
include "pmatring.mm"
include "w3a.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "cpmatpmat.mm"
include "cpmatel2.mm"
include "ralrimivva.mm"

theorem cpmatacl
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
  assert |- ( ( N e. Fin /\ R e. Ring ) -> A. x e. S A. y e. S ( x ( +g ` C ) y ) e. S )

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
    cplusg
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
    vi
    cv
    #
    vj
    cv
    #
    @6
    co
    #
    vc
    cv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    wceq
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @2
    @8
    @9
    @21
    @2
    @8
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @12
    @13
    @3
    co
    #
    va
    cv
    #
    @16
    cfv
    #
    wceq
    #
    va
    @19
    wrex
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    #
    @9
    @21
    wi
    @16
    @22
    cC
    cP
    cR
    cS
    vi
    vj
    va
    @19
    @3
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @22
    eqid
    #
    @19
    eqid
    #
    @16
    eqid
    #
    cpmatelimp2
    @2
    @9
    @30
    @21
    @2
    @9
    @4
    @22
    wcel
    #
    @12
    @13
    @4
    co
    #
    vb
    cv
    #
    @16
    cfv
    #
    wceq
    #
    vb
    @19
    wrex
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    @30
    @21
    wi
    #
    @16
    @22
    cC
    cP
    cR
    cS
    vi
    vj
    vb
    @19
    @4
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @31
    @32
    @33
    cpmatelimp2
    @2
    @34
    @40
    @41
    @2
    @34
    @30
    @40
    @21
    @2
    @34
    @30
    @40
    @21
    wi
    #
    wi
    @2
    @34
    wa
    @23
    @29
    @42
    @2
    @34
    @23
    @29
    @42
    wi
    @2
    @34
    @23
    wa
    #
    wa
    #
    @29
    @40
    @21
    @29
    @40
    wa
    @28
    @39
    wa
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @44
    @21
    @28
    @39
    vi
    vj
    cN
    cN
    r19.26-2
    @44
    @45
    @20
    vi
    vj
    cN
    cN
    @44
    @12
    cN
    wcel
    @13
    cN
    wcel
    wa
    #
    wa
    #
    @28
    @39
    @20
    @47
    @27
    @39
    @20
    wi
    va
    @19
    @47
    @25
    @19
    wcel
    #
    wa
    #
    @39
    @27
    @20
    @49
    @38
    @27
    @20
    wi
    #
    vb
    @19
    @47
    @48
    @36
    @19
    wcel
    #
    @38
    @50
    wi
    @47
    @48
    @51
    wa
    #
    wa
    #
    @38
    @27
    @20
    @53
    @38
    @27
    wa
    #
    @20
    @53
    @54
    wa
    #
    @18
    @14
    @25
    @36
    cP
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    @16
    cfv
    #
    wceq
    #
    vc
    @58
    @19
    @53
    @58
    @19
    wcel
    #
    @54
    @47
    @52
    @61
    @1
    @52
    @61
    wi
    @0
    @43
    @46
    @1
    @52
    @61
    @1
    @52
    wa
    @61
    @25
    @36
    cR
    cplusg
    cfv
    #
    co
    #
    @19
    wcel
    #
    @1
    @48
    @51
    @64
    @19
    @62
    cR
    @25
    @36
    @32
    @62
    eqid
    ringacl
    3expb
    @1
    @61
    @64
    wb
    @52
    @1
    @58
    @63
    @19
    @1
    @57
    @62
    @25
    @36
    @1
    @56
    cR
    cplusg
    @1
    cR
    @56
    cP
    cR
    crg
    cpmatsrngpmat.p
    ply1sca
    #
    eqcomd
    fveq2d
    oveqd
    eleq1d
    adantr
    mpbird
    ex
    ad3antlr
    imp
    adantr
    @15
    @58
    wceq
    #
    @18
    @60
    wb
    @55
    @66
    @17
    @59
    @14
    @15
    @58
    @16
    fveq2
    eqeq2d
    adantl
    @55
    @14
    @24
    @35
    cP
    cplusg
    cfv
    #
    co
    #
    @59
    @55
    @23
    @34
    wa
    #
    @46
    wa
    #
    @14
    @68
    wceq
    @47
    @70
    @52
    @54
    @44
    @69
    @46
    @44
    @34
    @23
    @2
    @43
    simpr
    ancomd
    anim1i
    ad2antrr
    cC
    @22
    @67
    @5
    cP
    @12
    @13
    cN
    @3
    @4
    cpmatsrngpmat.c
    @31
    @5
    eqid
    #
    @67
    eqid
    #
    matplusgcell
    syl
    @54
    @53
    @68
    @26
    @37
    @67
    co
    #
    @59
    @27
    @38
    @68
    @73
    wceq
    @24
    @26
    @35
    @37
    @67
    oveq12
    ancoms
    @53
    @59
    @73
    @53
    @16
    @56
    cP
    cghm
    co
    wcel
    @25
    @56
    cbs
    cfv
    #
    wcel
    #
    @36
    @74
    wcel
    #
    @59
    @73
    wceq
    @53
    @16
    @56
    cP
    @33
    @56
    eqid
    @1
    cP
    crg
    wcel
    @0
    @43
    @46
    @52
    cP
    cR
    cpmatsrngpmat.p
    ply1ring
    ad4antlr
    @1
    cP
    clmod
    wcel
    @0
    @43
    @46
    @52
    cP
    cR
    cpmatsrngpmat.p
    ply1lmod
    ad4antlr
    asclghm
    @47
    @52
    @75
    @47
    @48
    @75
    @51
    @2
    @48
    @75
    wi
    @43
    @46
    @2
    @48
    @75
    @2
    @19
    @74
    @25
    @2
    cR
    @56
    cbs
    @1
    cR
    @56
    wceq
    #
    @0
    @65
    adantl
    fveq2d
    eleq2d
    biimpd
    ad2antrr
    adantrd
    imp
    @47
    @52
    @76
    @47
    @51
    @76
    @48
    @47
    @51
    @76
    @47
    @19
    @74
    @36
    @47
    cR
    @56
    cbs
    @1
    @77
    @0
    @43
    @46
    @65
    ad3antlr
    fveq2d
    eleq2d
    biimpd
    adantld
    imp
    @57
    @67
    @56
    cP
    @25
    @16
    @36
    @74
    @74
    eqid
    @57
    eqid
    @72
    ghmlin
    syl3anc
    eqcomd
    sylan9eqr
    eqtrd
    rspcedvd
    ex
    expd
    anassrs
    rexlimdva
    com23
    rexlimdva
    impd
    ralimdvva
    syl5bir
    expd
    expr
    impd
    ex
    com34
    impd
    syld
    com23
    syld
    imp32
    @11
    @0
    @1
    @6
    @22
    wcel
    #
    @7
    @21
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
    @23
    @34
    @78
    @2
    @79
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
    @23
    @11
    @2
    @8
    wa
    @80
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
    @22
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
    @31
    cpmatpmat
    syl
    @11
    @0
    @1
    @9
    w3a
    #
    @34
    @11
    @2
    @9
    wa
    @81
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
    @22
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
    @31
    cpmatpmat
    syl
    @22
    @5
    cC
    @3
    @4
    @31
    @71
    ringacl
    syl3anc
    @16
    @22
    cC
    cP
    cR
    cS
    vi
    vj
    vc
    @19
    @6
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @31
    @32
    @33
    cpmatel2
    syl3anc
    mpbird
    ralrimivva
end
