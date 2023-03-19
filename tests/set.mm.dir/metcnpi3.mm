include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnp.mm"
include "co.mm"
include "crp.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cle.mm"
include "wrex.mm"
include "metcnpi2.mm"
include "c2.mm"
include "cdiv.mm"
include "rphalfcl.mm"
include "ad2antrl.mm"
include "cxr.mm"
include "simplll.mm"
include "simprr.mm"
include "cuni.mm"
include "simplrl.mm"
include "eqid.mm"
include "cnprcl.mm"
include "syl.mm"
include "wceq.mm"
include "mopnuni.mm"
include "eleqtrrd.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "rpxrd.mm"
include "rpxr.mm"
include "rphalflt.mm"
include "w3a.mm"
include "xrlelttr.mm"
include "expcomd.mm"
include "imp.mm"
include "syl31anc.mm"
include "simpllr.mm"
include "ctopon.mm"
include "wf.mm"
include "mopntopon.mm"
include "cnpf2.mm"
include "ffvelrnd.mm"
include "simplrr.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "imim12d.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "impr.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimddv.mm"

theorem metcnpi3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cZ: class Z
  let cB: class B
  let cE: class E
  let cL: class L
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint P x
  disjoint P y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K z
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint Z t
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P z
  disjoint L t
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  assert |- ( ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) ) /\ ( F e. ( ( J CnP K ) ` P ) /\ A e. RR+ ) ) -> E. x e. RR+ A. y e. X ( ( y C P ) <_ x -> ( ( F ` y ) D ( F ` P ) ) <_ A ) )

  proof
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cY
    cxmt
    cfv
    wcel
    #
    wa
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cA
    crp
    wcel
    #
    wa
    #
    wa
    #
    vy
    cv
    #
    cP
    cC
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    @7
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    cD
    co
    #
    cA
    clt
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    @8
    vx
    cv
    #
    cle
    wbr
    #
    @13
    cA
    cle
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    crp
    wrex
    #
    vz
    crp
    vz
    vy
    cA
    cC
    cD
    cP
    cF
    cJ
    cK
    cX
    cY
    metcn.2
    metcn.4
    metcnpi2
    @6
    @9
    crp
    wcel
    #
    @16
    wa
    wa
    @9
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @8
    @24
    cle
    wbr
    #
    @19
    wi
    #
    vy
    cX
    wral
    #
    @22
    @23
    @25
    @6
    @16
    @9
    rphalfcl
    #
    ad2antrl
    @6
    @23
    @16
    @28
    @6
    @23
    wa
    @15
    @27
    vy
    cX
    @6
    @23
    @7
    cX
    wcel
    #
    @15
    @27
    wi
    @6
    @23
    @30
    wa
    #
    wa
    #
    @26
    @10
    @14
    @19
    @32
    @8
    cxr
    wcel
    #
    @24
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    @24
    @9
    clt
    wbr
    #
    @26
    @10
    wi
    #
    @32
    @0
    @30
    cP
    cX
    wcel
    @33
    @0
    @1
    @5
    @31
    simplll
    #
    @6
    @23
    @30
    simprr
    #
    @32
    cP
    cJ
    cuni
    #
    cX
    @32
    @3
    cP
    @40
    wcel
    @2
    @3
    @4
    @31
    simplrl
    #
    cP
    cF
    cJ
    cK
    @40
    @40
    eqid
    cnprcl
    syl
    @32
    @0
    cX
    @40
    wceq
    @38
    cC
    cJ
    cX
    metcn.2
    mopnuni
    syl
    eleqtrrd
    #
    @7
    cP
    cC
    cX
    xmetcl
    syl3anc
    @32
    @24
    @23
    @25
    @6
    @30
    @29
    ad2antrl
    rpxrd
    @23
    @35
    @6
    @30
    @9
    rpxr
    ad2antrl
    @23
    @36
    @6
    @30
    @9
    rphalflt
    ad2antrl
    @33
    @34
    @35
    w3a
    #
    @36
    @37
    @43
    @26
    @36
    @10
    @8
    @24
    @9
    xrlelttr
    expcomd
    imp
    syl31anc
    @32
    @13
    cxr
    wcel
    #
    cA
    cxr
    wcel
    @14
    @19
    wi
    @32
    @1
    @11
    cY
    wcel
    @12
    cY
    wcel
    @44
    @0
    @1
    @5
    @31
    simpllr
    #
    @32
    cX
    cY
    @7
    cF
    @32
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @3
    cX
    cY
    cF
    wf
    @32
    @0
    @46
    @38
    cC
    cJ
    cX
    metcn.2
    mopntopon
    syl
    @32
    @1
    @47
    @45
    cD
    cK
    cY
    metcn.4
    mopntopon
    syl
    @41
    cP
    cF
    cJ
    cK
    cX
    cY
    cnpf2
    syl3anc
    #
    @39
    ffvelrnd
    @32
    cX
    cY
    cP
    cF
    @48
    @42
    ffvelrnd
    @11
    @12
    cD
    cY
    xmetcl
    syl3anc
    @32
    cA
    @2
    @3
    @4
    @31
    simplrr
    rpxrd
    @13
    cA
    xrltle
    syl2anc
    imim12d
    anassrs
    ralimdva
    impr
    @21
    @28
    vx
    @24
    crp
    @17
    @24
    wceq
    #
    @20
    @27
    vy
    cX
    @49
    @18
    @26
    @19
    @17
    @24
    @8
    cle
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rexlimddv
end
