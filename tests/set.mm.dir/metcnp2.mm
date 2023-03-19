include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "metcnp.mm"
include "wb.mm"
include "wceq.mm"
include "simpl1.mm"
include "ad2antrr.mm"
include "simpl3.mm"
include "simpr.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "breq1d.mm"
include "simpl2.mm"
include "simpllr.mm"
include "ffvelrnd.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem metcnp2
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
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
  let vx: setvar x
  let cZ: class Z
  let cA: class A
  let cB: class B
  let cE: class E
  let cL: class L
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )

  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y y
  disjoint Y z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint P w
  disjoint P y
  disjoint P z
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
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y x
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
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint D u
  disjoint D v
  disjoint D x
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
  disjoint P x
  disjoint L t
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) /\ P e. X ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. RR+ E. z e. RR+ A. w e. X ( ( w C P ) < z -> ( ( F ` w ) D ( F ` P ) ) < y ) ) ) )

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
    cP
    cX
    wcel
    #
    w3a
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    cX
    cY
    cF
    wf
    #
    cP
    vw
    cv
    #
    cC
    co
    #
    vz
    cv
    #
    clt
    wbr
    #
    cP
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    cD
    co
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cX
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    @4
    @5
    cP
    cC
    co
    #
    @7
    clt
    wbr
    #
    @10
    @9
    cD
    co
    #
    @12
    clt
    wbr
    #
    wi
    #
    vw
    cX
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wa
    vy
    vz
    vw
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
    metcnp
    @3
    @4
    @17
    @25
    @3
    @4
    wa
    #
    @16
    @24
    vy
    crp
    @26
    @12
    crp
    wcel
    #
    wa
    @15
    @23
    vz
    crp
    @26
    @27
    @7
    crp
    wcel
    #
    @15
    @23
    wb
    @26
    @27
    @28
    wa
    #
    wa
    #
    @14
    @22
    vw
    cX
    @30
    @5
    cX
    wcel
    #
    wa
    #
    @8
    @19
    @13
    @21
    @32
    @6
    @18
    @7
    clt
    @32
    @0
    @2
    @31
    @6
    @18
    wceq
    @26
    @0
    @29
    @31
    @0
    @1
    @2
    @4
    simpl1
    ad2antrr
    @26
    @2
    @29
    @31
    @0
    @1
    @2
    @4
    simpl3
    ad2antrr
    #
    @30
    @31
    simpr
    #
    cP
    @5
    cC
    cX
    xmetsym
    syl3anc
    breq1d
    @32
    @11
    @20
    @12
    clt
    @32
    @1
    @9
    cY
    wcel
    @10
    cY
    wcel
    @11
    @20
    wceq
    @26
    @1
    @29
    @31
    @0
    @1
    @2
    @4
    simpl2
    ad2antrr
    @32
    cX
    cY
    cP
    cF
    @3
    @4
    @29
    @31
    simpllr
    #
    @33
    ffvelrnd
    @32
    cX
    cY
    @5
    cF
    @35
    @34
    ffvelrnd
    @9
    @10
    cD
    cY
    xmetsym
    syl3anc
    breq1d
    imbi12d
    ralbidva
    anassrs
    rexbidva
    ralbidva
    pm5.32da
    bitrd
end
