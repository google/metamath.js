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
include "wrex.mm"
include "wf.mm"
include "simpr.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "cuni.mm"
include "eqid.mm"
include "cnprcl.mm"
include "adantl.mm"
include "wceq.mm"
include "mopnuni.mm"
include "ad2antrr.mm"
include "eleqtrrd.mm"
include "metcnp2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "rspccv.mm"
include "syl.mm"
include "impr.mm"

theorem metcnpi2
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
  assert |- ( ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) ) /\ ( F e. ( ( J CnP K ) ` P ) /\ A e. RR+ ) ) -> E. x e. RR+ A. y e. X ( ( y C P ) < x -> ( ( F ` y ) D ( F ` P ) ) < A ) )

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
    vy
    cv
    #
    cP
    cC
    co
    vx
    cv
    clt
    wbr
    #
    @5
    cF
    cfv
    cP
    cF
    cfv
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
    vx
    crp
    wrex
    #
    @2
    @3
    wa
    #
    @6
    @7
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cX
    wral
    vx
    crp
    wrex
    #
    vz
    crp
    wral
    #
    @4
    @10
    wi
    @11
    cX
    cY
    cF
    wf
    #
    @16
    @11
    @3
    @17
    @16
    wa
    #
    @2
    @3
    simpr
    @11
    @0
    @1
    cP
    cX
    wcel
    @3
    @18
    wb
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    @11
    cP
    cJ
    cuni
    #
    cX
    @3
    cP
    @19
    wcel
    @2
    cP
    cF
    cJ
    cK
    @19
    @19
    eqid
    cnprcl
    adantl
    @0
    cX
    @19
    wceq
    @1
    @3
    cC
    cJ
    cX
    metcn.2
    mopnuni
    ad2antrr
    eleqtrrd
    vz
    vx
    vy
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
    metcnp2
    syl3anc
    mpbid
    simprd
    @15
    @10
    vz
    cA
    crp
    @12
    cA
    wceq
    #
    @14
    @9
    vx
    vy
    crp
    cX
    @20
    @13
    @8
    @6
    @12
    cA
    @7
    clt
    breq2
    imbi2d
    rexralbidv
    rspccv
    syl
    impr
end
