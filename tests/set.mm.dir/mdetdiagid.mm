include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "weq.mm"
include "cif.mm"
include "wceq.mm"
include "wral.mm"
include "cfv.mm"
include "chash.mm"
include "cmpt.mm"
include "cgsu.mm"
include "w3a.mm"
include "wne.mm"
include "wi.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "3jca.mm"
include "id.mm"
include "ifnefalse.mm"
include "sylan9eqr.mm"
include "exp31.mm"
include "com23.mm"
include "ralimdva.mm"
include "imp.mm"
include "mdetdiag.mm"
include "sylc.mm"
include "oveq1.mm"
include "equequ1.mm"
include "ifbid.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "equequ2.mm"
include "rspc2v.mm"
include "anidms.mm"
include "equid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "an32s.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "cmnmnd.mm"
include "syl.mm"
include "mgpbas.mm"
include "gsumconst.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem mdetdiagid
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vp: setvar p
  assume mdetdiag.d: |- D = ( N maDet R )
  assume mdetdiag.a: |- A = ( N Mat R )
  assume mdetdiag.b: |- B = ( Base ` A )
  assume mdetdiag.g: |- G = ( mulGrp ` R )
  assume mdetdiag.0: |- .0. = ( 0g ` R )
  assume mdetdiagid.c: |- C = ( Base ` R )
  assume mdetdiagid.t: |- .x. = ( .g ` G )

  disjoint M i
  disjoint M j
  disjoint i j
  disjoint N i
  disjoint N j
  disjoint .0. i
  disjoint .0. j
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint B k
  disjoint B p
  disjoint k p
  disjoint G k
  disjoint G p
  disjoint M k
  disjoint M p
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint N k
  disjoint N p
  disjoint R k
  disjoint R p
  disjoint .0. k
  disjoint .0. p
  disjoint C k
  disjoint X k
  assert |- ( ( ( R e. CRing /\ N e. Fin ) /\ ( M e. B /\ X e. C ) ) -> ( A. i e. N A. j e. N ( i M j ) = if ( i = j , X , .0. ) -> ( D ` M ) = ( ( # ` N ) .x. X ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cM
    cB
    wcel
    #
    cX
    cC
    wcel
    #
    wa
    #
    wa
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    vi
    vj
    weq
    #
    cX
    c.0
    cif
    #
    wceq
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    cM
    cD
    cfv
    #
    cN
    chash
    cfv
    cX
    c.x
    co
    #
    wceq
    @6
    @14
    wa
    #
    @15
    cG
    vk
    cN
    vk
    cv
    #
    @18
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    cN
    cX
    cmpt
    #
    cgsu
    co
    #
    @16
    @17
    @0
    @1
    @3
    w3a
    #
    @7
    @8
    wne
    #
    @9
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    @15
    @21
    wceq
    @6
    @24
    @14
    @6
    @0
    @1
    @3
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    #
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    3jca
    adantr
    @6
    @14
    @29
    @6
    @13
    @28
    vi
    cN
    @6
    @7
    cN
    wcel
    wa
    #
    @12
    @27
    vj
    cN
    @31
    @8
    cN
    wcel
    wa
    #
    @25
    @12
    @26
    @32
    @25
    @12
    @26
    @12
    @32
    @25
    wa
    @9
    @11
    c.0
    @12
    id
    @25
    @11
    c.0
    wceq
    @32
    @7
    @8
    cX
    c.0
    ifnefalse
    adantl
    sylan9eqr
    exp31
    com23
    ralimdva
    ralimdva
    imp
    cA
    cB
    cD
    cR
    vi
    vj
    vk
    cG
    cM
    cN
    c.0
    mdetdiag.d
    mdetdiag.a
    mdetdiag.b
    mdetdiag.g
    mdetdiag.0
    mdetdiag
    sylc
    @17
    @20
    @22
    cG
    cgsu
    @17
    vk
    cN
    @19
    cX
    @6
    @18
    cN
    wcel
    #
    @14
    @19
    cX
    wceq
    @6
    @33
    wa
    #
    @14
    wa
    @19
    vk
    vk
    weq
    #
    cX
    c.0
    cif
    #
    cX
    @34
    @14
    @19
    @36
    wceq
    #
    @33
    @14
    @37
    wi
    #
    @6
    @33
    @38
    @12
    @37
    @18
    @8
    cM
    co
    #
    vk
    vj
    weq
    #
    cX
    c.0
    cif
    #
    wceq
    vi
    vj
    @18
    @18
    cN
    cN
    vi
    vk
    weq
    #
    @9
    @39
    @11
    @41
    @7
    @18
    @8
    cM
    oveq1
    @42
    @10
    @40
    cX
    c.0
    vi
    vk
    vj
    equequ1
    ifbid
    eqeq12d
    vj
    vk
    weq
    #
    @39
    @19
    @41
    @36
    @8
    @18
    @18
    cM
    oveq2
    @43
    @40
    @35
    cX
    c.0
    vj
    vk
    vk
    equequ2
    ifbid
    eqeq12d
    rspc2v
    anidms
    adantl
    imp
    @35
    cX
    c.0
    vk
    equid
    iftruei
    syl6eq
    an32s
    mpteq2dva
    oveq2d
    @6
    @23
    @16
    wceq
    #
    @14
    @6
    cG
    cmnd
    wcel
    #
    @1
    @4
    @44
    @2
    @45
    @5
    @0
    @45
    @1
    @0
    cG
    ccmn
    wcel
    @45
    cR
    cG
    mdetdiag.g
    crngmgp
    cG
    cmnmnd
    syl
    adantr
    adantr
    @30
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    cN
    cC
    c.x
    vk
    cG
    cX
    cC
    cR
    cG
    mdetdiag.g
    mdetdiagid.c
    mgpbas
    mdetdiagid.t
    gsumconst
    syl3anc
    adantr
    3eqtrd
    ex
end
