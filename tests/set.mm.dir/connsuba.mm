include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "resttopon.mm"
include "dfconn2.mm"
include "syl.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "a1i.mm"
include "wrex.mm"
include "toponmax.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "elrest.mm"
include "syldan.mm"
include "simplr.mm"
include "neeq1d.mm"
include "ineq12d.mm"
include "inindir.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "uneq12d.mm"
include "indir.mm"
include "imbi12d.mm"
include "ralxfr2d.mm"
include "bitrd.mm"

theorem connsuba
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let cS: class S

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint J u
  disjoint J v
  disjoint S x
  disjoint S y
  disjoint X u
  disjoint X v
  assert |- ( ( J e. ( TopOn ` X ) /\ A C_ X ) -> ( ( J |`t A ) e. Conn <-> A. x e. J A. y e. J ( ( ( x i^i A ) =/= (/) /\ ( y i^i A ) =/= (/) /\ ( ( x i^i y ) i^i A ) = (/) ) -> ( ( x u. y ) i^i A ) =/= A ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    cconn
    wcel
    #
    vu
    cv
    #
    c0
    wne
    #
    vv
    cv
    #
    c0
    wne
    #
    @6
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @6
    @8
    cun
    #
    cA
    wne
    #
    wi
    #
    vv
    @4
    wral
    #
    vu
    @4
    wral
    #
    vx
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    vy
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    @18
    @21
    cin
    cA
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @18
    @21
    cun
    cA
    cin
    #
    cA
    wne
    #
    wi
    #
    vy
    cJ
    wral
    #
    vx
    cJ
    wral
    @3
    @4
    cA
    ctopon
    cfv
    wcel
    @5
    @17
    wb
    cA
    cJ
    cX
    resttopon
    vu
    vv
    @4
    cA
    dfconn2
    syl
    @3
    @16
    @30
    vu
    vx
    @19
    @4
    cJ
    cvv
    @19
    cvv
    wcel
    @3
    @18
    cJ
    wcel
    wa
    @18
    cA
    vx
    vex
    inex1
    a1i
    @1
    @2
    cA
    cvv
    wcel
    #
    @6
    @4
    wcel
    @6
    @19
    wceq
    #
    vx
    cJ
    wrex
    wb
    @3
    cA
    cX
    cJ
    @1
    cX
    cJ
    wcel
    @2
    cX
    cJ
    toponmax
    adantr
    @1
    @2
    simpr
    ssexd
    #
    vx
    @6
    cA
    cJ
    @0
    cvv
    elrest
    syldan
    @3
    @32
    wa
    #
    @15
    @29
    vv
    vy
    @22
    @4
    cJ
    cvv
    @22
    cvv
    wcel
    @34
    @21
    cJ
    wcel
    wa
    @21
    cA
    vy
    vex
    inex1
    a1i
    @3
    @8
    @4
    wcel
    @8
    @22
    wceq
    #
    vy
    cJ
    wrex
    wb
    #
    @32
    @1
    @2
    @31
    @36
    @33
    vy
    @8
    cA
    cJ
    @0
    cvv
    elrest
    syldan
    adantr
    @34
    @35
    wa
    #
    @12
    @26
    @14
    @28
    @37
    @7
    @20
    @9
    @23
    @11
    @25
    @37
    @6
    @19
    c0
    @3
    @32
    @35
    simplr
    #
    neeq1d
    @37
    @8
    @22
    c0
    @34
    @35
    simpr
    #
    neeq1d
    @37
    @10
    @24
    c0
    @37
    @10
    @19
    @22
    cin
    @24
    @37
    @6
    @19
    @8
    @22
    @38
    @39
    ineq12d
    @18
    @21
    cA
    inindir
    syl6eqr
    eqeq1d
    3anbi123d
    @37
    @13
    @27
    cA
    @37
    @13
    @19
    @22
    cun
    @27
    @37
    @6
    @19
    @8
    @22
    @38
    @39
    uneq12d
    @18
    @21
    cA
    indir
    syl6eqr
    neeq1d
    imbi12d
    ralxfr2d
    ralxfr2d
    bitrd
end
