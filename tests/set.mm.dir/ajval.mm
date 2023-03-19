include "ccphlo.mm"
include "wcel.mm"
include "cnv.mm"
include "wf.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "copab.mm"
include "wa.mm"
include "cio.mm"
include "phnv.mm"
include "ajfval.mm"
include "sylan.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "cvv.mm"
include "cba.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "mpan2.mm"
include "eqid.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "3anbi13d.mm"
include "fvopab5.mm"
include "syl.mm"
include "3anass.mm"
include "baib.mm"
include "iotabidv.mm"
include "eqtrd.mm"
include "3ad2ant3.mm"

theorem ajval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  assume ajval.1: |- X = ( BaseSet ` U )
  assume ajval.2: |- Y = ( BaseSet ` W )
  assume ajval.3: |- P = ( .iOLD ` U )
  assume ajval.4: |- Q = ( .iOLD ` W )
  assume ajval.5: |- A = ( U adj W )

  disjoint s x
  disjoint s y
  disjoint T s
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint U s
  disjoint U x
  disjoint U y
  disjoint W s
  disjoint W x
  disjoint W y
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y y
  disjoint P t
  disjoint Q t
  disjoint s t
  disjoint t x
  disjoint t y
  disjoint T t
  disjoint U t
  disjoint W t
  disjoint X t
  disjoint Y t
  assert |- ( ( U e. CPreHilOLD /\ W e. NrmCVec /\ T : X --> Y ) -> ( A ` T ) = ( iota s ( s : Y --> X /\ A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cW
    cnv
    wcel
    #
    cX
    cY
    cT
    wf
    #
    w3a
    cT
    cA
    cfv
    #
    cT
    cX
    cY
    vt
    cv
    #
    wf
    #
    cY
    cX
    vs
    cv
    #
    wf
    #
    vx
    cv
    #
    @4
    cfv
    #
    vy
    cv
    #
    cQ
    co
    #
    @8
    @10
    @6
    cfv
    cP
    co
    #
    wceq
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    w3a
    #
    vt
    vs
    copab
    #
    cfv
    #
    @7
    @8
    cT
    cfv
    #
    @10
    cQ
    co
    #
    @12
    wceq
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    wa
    #
    vs
    cio
    #
    @0
    @1
    @3
    @17
    wceq
    @2
    @0
    @1
    wa
    cT
    cA
    @16
    @0
    cU
    cnv
    wcel
    @1
    cA
    @16
    wceq
    cU
    phnv
    vx
    vy
    vt
    cA
    cP
    cQ
    cU
    cW
    cX
    cY
    vs
    ajval.1
    ajval.2
    ajval.3
    ajval.4
    ajval.5
    ajfval
    sylan
    fveq1d
    3adant3
    @2
    @0
    @17
    @23
    wceq
    @1
    @2
    @17
    @2
    @7
    @21
    w3a
    #
    vs
    cio
    #
    @23
    @2
    cT
    cvv
    wcel
    #
    @17
    @25
    wceq
    @2
    cX
    cvv
    wcel
    @26
    cX
    cU
    cba
    cfv
    cvv
    ajval.1
    cU
    cba
    fvex
    eqeltri
    cX
    cY
    cvv
    cT
    fex
    mpan2
    @15
    @24
    vt
    vs
    cT
    @16
    cvv
    @16
    eqid
    @4
    cT
    wceq
    #
    @5
    @2
    @14
    @21
    @7
    cX
    cY
    @4
    cT
    feq1
    @27
    @13
    @20
    vx
    vy
    cX
    cY
    @27
    @11
    @19
    @12
    @27
    @9
    @18
    @10
    cQ
    @8
    @4
    cT
    fveq1
    oveq1d
    eqeq1d
    2ralbidv
    3anbi13d
    fvopab5
    syl
    @2
    @24
    @22
    vs
    @24
    @2
    @22
    @2
    @7
    @21
    3anass
    baib
    iotabidv
    eqtrd
    3ad2ant3
    eqtrd
end
