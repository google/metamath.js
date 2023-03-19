include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "cpw.mm"
include "clmod.mm"
include "wi.mm"
include "wa.mm"
include "cvv.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "difexg.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "adantr.mm"
include "cv.mm"
include "cmpt.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "syl.mm"
include "funmpt2.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simpr.mm"
include "fsuppimpd.mm"
include "wfn.mm"
include "wceq.mm"
include "wral.mm"
include "simplr.mm"
include "simpll.mm"
include "eldifi.mm"
include "lincresunitlem2.mm"
include "syl21anc.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "elmapfn.mm"
include "jca.mm"
include "difssd.mm"
include "simpr1.mm"
include "3jca.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "simpllr.mm"
include "fvmptd.mm"
include "oveq2.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant2.mm"
include "lincresunitlem1.mm"
include "ancoms.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "ex.mm"
include "suppfnss.mm"
include "imp.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "com23.mm"
include "3impia.mm"
include "impcom.mm"

theorem lincresunit2
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k
  assume lincresunit.b: |- B = ( Base ` M )
  assume lincresunit.r: |- R = ( Scalar ` M )
  assume lincresunit.e: |- E = ( Base ` R )
  assume lincresunit.u: |- U = ( Unit ` R )
  assume lincresunit.0: |- .0. = ( 0g ` R )
  assume lincresunit.z: |- Z = ( 0g ` M )
  assume lincresunit.n: |- N = ( invg ` R )
  assume lincresunit.i: |- I = ( invr ` R )
  assume lincresunit.t: |- .x. = ( .r ` R )
  assume lincresunit.g: |- G = ( s e. ( S \ { X } ) |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) )

  disjoint .0. s
  disjoint B s
  disjoint E s
  disjoint F s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint U s
  disjoint I s
  disjoint N s
  disjoint .x. s
  disjoint B x
  disjoint E x
  disjoint F x
  disjoint G x
  disjoint M x
  disjoint N x
  disjoint S x
  disjoint U x
  disjoint X x
  disjoint .0. x
  disjoint s x
  disjoint k x
  assert |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ F finSupp .0. ) ) -> G finSupp .0. )

  proof
    cF
    cE
    cS
    cmap
    co
    wcel
    #
    cX
    cF
    cfv
    #
    cU
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    w3a
    cS
    cB
    cpw
    #
    wcel
    #
    cM
    clmod
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cG
    c.0
    cfsupp
    wbr
    #
    @0
    @2
    @3
    @8
    @9
    wi
    @0
    @2
    wa
    #
    @8
    @3
    @9
    @10
    @8
    @3
    @9
    wi
    @10
    @8
    wa
    #
    @3
    @9
    @11
    @3
    wa
    #
    cG
    cvv
    wcel
    #
    cG
    wfun
    #
    c.0
    cvv
    wcel
    #
    cF
    c.0
    csupp
    co
    #
    cfn
    wcel
    cG
    c.0
    csupp
    co
    @16
    wss
    #
    @9
    @12
    cS
    cX
    csn
    #
    cdif
    #
    cvv
    wcel
    #
    @13
    @11
    @20
    @3
    @8
    @20
    @10
    @5
    @6
    @20
    @7
    cS
    @18
    @4
    difexg
    3ad2ant1
    adantl
    adantr
    @20
    cG
    vs
    @19
    @1
    cN
    cfv
    cI
    cfv
    #
    vs
    cv
    #
    cF
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cvv
    lincresunit.g
    vs
    @19
    @24
    cvv
    mptexg
    syl5eqel
    syl
    @14
    @12
    vs
    @19
    @24
    cG
    lincresunit.g
    funmpt2
    a1i
    @15
    @12
    c.0
    cR
    c0g
    cfv
    cvv
    lincresunit.0
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    @12
    cF
    c.0
    @11
    @3
    simpr
    fsuppimpd
    @11
    @17
    @3
    @11
    cG
    @19
    wfn
    #
    cF
    cS
    wfn
    #
    wa
    #
    @19
    cS
    wss
    #
    @5
    @15
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    #
    c.0
    wceq
    #
    @32
    cG
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    @19
    wral
    #
    @17
    @11
    @27
    @28
    @11
    @24
    cE
    wcel
    #
    vs
    @19
    wral
    @27
    @11
    @39
    vs
    @19
    @11
    @22
    @19
    wcel
    #
    wa
    @8
    @10
    @22
    cS
    wcel
    #
    @39
    @10
    @8
    @40
    simplr
    @10
    @8
    @40
    simpll
    @40
    @41
    @11
    @22
    cS
    @18
    eldifi
    adantl
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    @22
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunitlem2
    syl21anc
    ralrimiva
    vs
    @19
    @24
    cG
    cE
    lincresunit.g
    fnmpt
    syl
    @10
    @28
    @8
    @0
    @28
    @2
    cF
    cE
    cS
    elmapfn
    adantr
    adantr
    jca
    @11
    @30
    @5
    @15
    @11
    cS
    @18
    difssd
    @10
    @5
    @6
    @7
    simpr1
    @15
    @11
    @26
    a1i
    3jca
    @11
    @37
    vx
    @19
    @11
    @32
    @19
    wcel
    #
    wa
    #
    @34
    @36
    @43
    @34
    wa
    #
    @35
    @21
    @33
    c.x
    co
    #
    c.0
    @44
    vs
    @32
    @24
    @45
    @19
    cG
    cE
    cG
    @25
    wceq
    @44
    lincresunit.g
    a1i
    @22
    @32
    wceq
    #
    @24
    @45
    wceq
    @44
    @46
    @23
    @33
    @21
    c.x
    @22
    @32
    cF
    fveq2
    oveq2d
    adantl
    @11
    @42
    @34
    simplr
    @44
    @8
    @10
    @32
    cS
    wcel
    #
    @45
    cE
    wcel
    @10
    @8
    @42
    @34
    simpllr
    @43
    @10
    @34
    @10
    @8
    @42
    simpll
    adantr
    @43
    @47
    @34
    @42
    @47
    @11
    @32
    cS
    @18
    eldifi
    adantl
    adantr
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    @32
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunitlem2
    syl21anc
    fvmptd
    @34
    @43
    @45
    @21
    c.0
    c.x
    co
    #
    c.0
    @33
    c.0
    @21
    c.x
    oveq2
    @11
    @48
    c.0
    wceq
    #
    @42
    @11
    cR
    crg
    wcel
    #
    @21
    cE
    wcel
    #
    @49
    @8
    @50
    @10
    @6
    @5
    @50
    @7
    cR
    cM
    lincresunit.r
    lmodring
    3ad2ant2
    adantl
    @8
    @10
    @51
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunitlem1
    ancoms
    cE
    cR
    c.x
    @21
    c.0
    lincresunit.e
    lincresunit.t
    lincresunit.0
    ringrz
    syl2anc
    adantr
    sylan9eqr
    eqtrd
    ex
    ralrimiva
    @29
    @31
    wa
    @38
    @17
    vx
    @19
    cS
    cG
    cF
    @4
    cvv
    c.0
    suppfnss
    imp
    syl21anc
    adantr
    @16
    cG
    cvv
    cvv
    c.0
    suppssfifsupp
    syl32anc
    ex
    ex
    com23
    3impia
    impcom
end
