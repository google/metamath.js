include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "cngp.mm"
include "cbs.mm"
include "cr.mm"
include "ad2antrr.mm"
include "wf.mm"
include "cghm.mm"
include "eqid.mm"
include "ghmf.mm"
include "syl.mm"
include "simprl.mm"
include "ffvelrn.mm"
include "syl2anc.mm"
include "nmcl.mm"
include "crp.mm"
include "adantr.mm"
include "nmrpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "rerpdivcld.mm"
include "rexrd.mm"
include "cxr.mm"
include "nmocl.mm"
include "syl3anc.mm"
include "w3a.mm"
include "3jca.mm"
include "nmoi2.mm"
include "simplr.mm"
include "xrletrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmul.mm"
include "cc0.mm"
include "0le0.mm"
include "simpllr.mm"
include "recnd.mm"
include "mul01d.mm"
include "syl5breqr.mm"
include "c0g.mm"
include "fveq2.mm"
include "ghmid.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "ad3antrrr.mm"
include "nm0.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3brtr4d.mm"
include "a1d.mm"
include "simpr.mm"
include "3expa.mm"
include "sylanl1.mm"
include "ledivmul2d.mm"
include "biimpd.mm"
include "embantd.mm"
include "pm2.61dane.mm"
include "ralimdva.mm"
include "nmolb.mm"
include "syl311anc.mm"
include "syld.mm"
include "imp.mm"
include "an32s.mm"
include "pnfge.mm"
include "breqtrrd.mm"
include "wo.mm"
include "cmnf.mm"
include "ge0nemnf.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "impbida.mm"

theorem nmoleub
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )
  assume nmoi.2: |- V = ( Base ` S )
  assume nmoi.3: |- L = ( norm ` S )
  assume nmoi.4: |- M = ( norm ` T )
  assume nmoi2.z: |- .0. = ( 0g ` S )
  assume nmoleub.1: |- ( ph -> S e. NrmGrp )
  assume nmoleub.2: |- ( ph -> T e. NrmGrp )
  assume nmoleub.3: |- ( ph -> F e. ( S GrpHom T ) )
  assume nmoleub.4: |- ( ph -> A e. RR* )
  assume nmoleub.5: |- ( ph -> 0 <_ A )

  disjoint L x
  disjoint M x
  disjoint S x
  disjoint T x
  disjoint A x
  disjoint F x
  disjoint ph x
  disjoint V x
  disjoint N x
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint L f
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint L r
  disjoint s t
  disjoint s x
  disjoint L s
  disjoint t x
  disjoint L t
  disjoint M f
  disjoint M r
  disjoint M s
  disjoint M t
  disjoint S f
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint T f
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint A r
  disjoint A s
  disjoint F f
  disjoint F r
  disjoint F s
  disjoint V f
  disjoint V r
  disjoint V s
  disjoint V t
  disjoint X r
  disjoint X x
  disjoint N r
  disjoint N s
  disjoint N t
  assert |- ( ph -> ( ( N ` F ) <_ A <-> A. x e. V ( x =/= .0. -> ( ( M ` ( F ` x ) ) / ( L ` x ) ) <_ A ) ) )

  proof
    wph
    cF
    cN
    cfv
    #
    cA
    cle
    wbr
    #
    vx
    cv
    #
    c.0
    wne
    #
    @2
    cF
    cfv
    #
    cM
    cfv
    #
    @2
    cL
    cfv
    #
    cdiv
    co
    #
    cA
    cle
    wbr
    #
    wi
    #
    vx
    cV
    wral
    #
    wph
    @1
    wa
    #
    @9
    vx
    cV
    @11
    @2
    cV
    wcel
    #
    @3
    @8
    @11
    @12
    @3
    wa
    #
    wa
    #
    @7
    @0
    cA
    @14
    @7
    @14
    @5
    @6
    @14
    cT
    cngp
    wcel
    #
    @4
    cT
    cbs
    cfv
    #
    wcel
    #
    @5
    cr
    wcel
    #
    wph
    @15
    @1
    @13
    nmoleub.2
    ad2antrr
    @14
    cV
    @16
    cF
    wf
    #
    @12
    @17
    wph
    @19
    @1
    @13
    wph
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @19
    nmoleub.3
    cS
    cT
    cF
    cV
    @16
    nmoi.2
    @16
    eqid
    #
    ghmf
    syl
    #
    ad2antrr
    @11
    @12
    @3
    simprl
    cV
    @16
    @2
    cF
    ffvelrn
    #
    syl2anc
    @4
    cT
    cM
    @16
    @21
    nmoi.4
    nmcl
    #
    syl2anc
    @11
    cS
    cngp
    wcel
    #
    @13
    @6
    crp
    wcel
    #
    wph
    @25
    @1
    nmoleub.1
    adantr
    @25
    @12
    @3
    @26
    @2
    cS
    cL
    cV
    c.0
    nmoi.2
    nmoi.3
    nmoi2.z
    nmrpcl
    #
    3expb
    sylan
    rerpdivcld
    rexrd
    wph
    @0
    cxr
    wcel
    #
    @1
    @13
    wph
    @25
    @15
    @20
    @28
    nmoleub.1
    nmoleub.2
    nmoleub.3
    cS
    cT
    cF
    cN
    nmofval.1
    nmocl
    syl3anc
    #
    ad2antrr
    wph
    cA
    cxr
    wcel
    #
    @1
    @13
    nmoleub.4
    ad2antrr
    @11
    @25
    @15
    @20
    w3a
    #
    @13
    @7
    @0
    cle
    wbr
    wph
    @31
    @1
    wph
    @25
    @15
    @20
    nmoleub.1
    nmoleub.2
    nmoleub.3
    3jca
    adantr
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    @2
    c.0
    nmofval.1
    nmoi.2
    nmoi.3
    nmoi.4
    nmoi2.z
    nmoi2
    sylan
    wph
    @1
    @13
    simplr
    xrletrd
    expr
    ralrimiva
    wph
    @10
    wa
    #
    cA
    cr
    wcel
    #
    @1
    cA
    cpnf
    wceq
    #
    wph
    @33
    @10
    @1
    wph
    @33
    wa
    #
    @10
    @1
    @35
    @10
    @5
    cA
    @6
    cmul
    co
    #
    cle
    wbr
    #
    vx
    cV
    wral
    #
    @1
    @35
    @9
    @37
    vx
    cV
    @35
    @12
    wa
    #
    @9
    @37
    wi
    @2
    c.0
    @39
    @2
    c.0
    wceq
    #
    wa
    #
    @37
    @9
    @41
    cc0
    cA
    cc0
    cmul
    co
    #
    @5
    @36
    cle
    @41
    cc0
    cc0
    @42
    cle
    0le0
    @41
    cA
    @41
    cA
    wph
    @33
    @12
    @40
    simpllr
    recnd
    mul01d
    syl5breqr
    @41
    @5
    cT
    c0g
    cfv
    #
    cM
    cfv
    #
    cc0
    @41
    @4
    @43
    cM
    @40
    @39
    @4
    c.0
    cF
    cfv
    #
    @43
    @2
    c.0
    cF
    fveq2
    @39
    @20
    @45
    @43
    wceq
    wph
    @20
    @33
    @12
    nmoleub.3
    ad2antrr
    cS
    cT
    cF
    c.0
    @43
    nmoi2.z
    @43
    eqid
    #
    ghmid
    syl
    sylan9eqr
    fveq2d
    @41
    @15
    @44
    cc0
    wceq
    wph
    @15
    @33
    @12
    @40
    nmoleub.2
    ad3antrrr
    cT
    cM
    @43
    nmoi.4
    @46
    nm0
    syl
    eqtrd
    @41
    @6
    cc0
    cA
    cmul
    @40
    @39
    @6
    c.0
    cL
    cfv
    #
    cc0
    @2
    c.0
    cL
    fveq2
    @39
    @25
    @47
    cc0
    wceq
    wph
    @25
    @33
    @12
    nmoleub.1
    ad2antrr
    cS
    cL
    c.0
    nmoi.3
    nmoi2.z
    nm0
    syl
    sylan9eqr
    oveq2d
    3brtr4d
    a1d
    @39
    @3
    wa
    #
    @3
    @8
    @37
    @39
    @3
    simpr
    @48
    @8
    @37
    @48
    @5
    cA
    @6
    @39
    @18
    @3
    @39
    @15
    @17
    @18
    wph
    @15
    @33
    @12
    nmoleub.2
    ad2antrr
    @35
    @19
    @12
    @17
    wph
    @19
    @33
    @22
    adantr
    @23
    sylan
    @24
    syl2anc
    adantr
    wph
    @33
    @12
    @3
    simpllr
    @35
    @25
    @12
    @3
    @26
    wph
    @25
    @33
    nmoleub.1
    adantr
    #
    @25
    @12
    @3
    @26
    @27
    3expa
    sylanl1
    ledivmul2d
    biimpd
    embantd
    pm2.61dane
    ralimdva
    @35
    @25
    @15
    @20
    @33
    cc0
    cA
    cle
    wbr
    #
    @38
    @1
    wi
    @49
    wph
    @15
    @33
    nmoleub.2
    adantr
    wph
    @20
    @33
    nmoleub.3
    adantr
    wph
    @33
    simpr
    wph
    @50
    @33
    nmoleub.5
    adantr
    vx
    cA
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    nmofval.1
    nmoi.2
    nmoi.3
    nmoi.4
    nmolb
    syl311anc
    syld
    imp
    an32s
    @32
    @34
    wa
    #
    @0
    cpnf
    cA
    cle
    @51
    @28
    @0
    cpnf
    cle
    wbr
    wph
    @28
    @10
    @34
    @29
    ad2antrr
    @0
    pnfge
    syl
    @32
    @34
    simpr
    breqtrrd
    wph
    @33
    @34
    wo
    #
    @10
    wph
    @30
    cA
    cmnf
    wne
    #
    wa
    @52
    wph
    @30
    @53
    nmoleub.4
    wph
    @30
    @50
    @53
    nmoleub.4
    nmoleub.5
    cA
    ge0nemnf
    syl2anc
    jca
    cA
    xrnemnf
    sylib
    adantr
    mpjaodan
    impbida
end
