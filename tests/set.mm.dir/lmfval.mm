include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "ctop.mm"
include "clm.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-lm.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "unieqd.mm"
include "toponuni.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "raleqdv.mm"
include "3anbi123d.mm"
include "opabbidv.mm"
include "topontop.mm"
include "cxp.mm"
include "wss.mm"
include "df-3an.mm"
include "opabbii.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "ovex.mm"
include "toponmax.mm"
include "xpexg.mm"
include "sylancr.mm"
include "ssexg.mm"
include "fvmptd.mm"

theorem lmfval
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let cK: class K
  let cY: class Y
  let vv: setvar v

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint f u
  disjoint J f
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint K f
  disjoint j k
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint f v
  disjoint j u
  disjoint j v
  disjoint J j
  disjoint k u
  disjoint k v
  disjoint J k
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint J w
  assert |- ( J e. ( TopOn ` X ) -> ( ~~>t ` J ) = { <. f , x >. | ( f e. ( X ^pm CC ) /\ x e. X /\ A. u e. J ( x e. u -> E. y e. ran ZZ>= ( f |` y ) : y --> u ) ) } )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    vj
    cJ
    vf
    cv
    #
    vj
    cv
    #
    cuni
    #
    cc
    cpm
    co
    #
    wcel
    #
    vx
    cv
    #
    @3
    wcel
    #
    @6
    vu
    cv
    #
    wcel
    vy
    cv
    #
    @8
    @1
    @9
    cres
    wf
    vy
    cuz
    crn
    wrex
    wi
    #
    vu
    @2
    wral
    #
    w3a
    #
    vf
    vx
    copab
    #
    @1
    cX
    cc
    cpm
    co
    #
    wcel
    #
    @6
    cX
    wcel
    #
    @10
    vu
    cJ
    wral
    #
    w3a
    #
    vf
    vx
    copab
    #
    ctop
    clm
    cvv
    clm
    vj
    ctop
    @13
    cmpt
    wceq
    @0
    vx
    vy
    vu
    vf
    vj
    df-lm
    a1i
    @0
    @2
    cJ
    wceq
    #
    wa
    #
    @12
    @18
    vf
    vx
    @21
    @5
    @15
    @7
    @16
    @11
    @17
    @21
    @4
    @14
    @1
    @21
    @3
    cX
    cc
    cpm
    @21
    @3
    cJ
    cuni
    #
    cX
    @21
    @2
    cJ
    @0
    @20
    simpr
    #
    unieqd
    @0
    cX
    @22
    wceq
    @20
    cX
    cJ
    toponuni
    adantr
    eqtr4d
    #
    oveq1d
    eleq2d
    @21
    @3
    cX
    @6
    @24
    eleq2d
    @21
    @10
    vu
    @2
    cJ
    @23
    raleqdv
    3anbi123d
    opabbidv
    cX
    cJ
    topontop
    @0
    @19
    @14
    cX
    cxp
    #
    wss
    @25
    cvv
    wcel
    #
    @19
    cvv
    wcel
    @19
    @15
    @16
    wa
    @17
    wa
    #
    vf
    vx
    copab
    @25
    @18
    @27
    vf
    vx
    @15
    @16
    @17
    df-3an
    opabbii
    @17
    vf
    vx
    @14
    cX
    opabssxp
    eqsstri
    @0
    @14
    cvv
    wcel
    cX
    cJ
    wcel
    @26
    cX
    cc
    cpm
    ovex
    cX
    cJ
    toponmax
    @14
    cX
    cvv
    cJ
    xpexg
    sylancr
    @19
    @25
    cvv
    ssexg
    sylancr
    fvmptd
end
