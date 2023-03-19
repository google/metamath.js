include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "cfv.mm"
include "cab.mm"
include "cmpt.mm"
include "cvv.mm"
include "clp.mm"
include "wceq.mm"
include "topopn.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "cuni.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "abbidv.mm"
include "mpteq12dv.mm"
include "df-lp.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem lpfval
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let cP: class P
  let cS: class S
  let cT: class T
  assume lpfval.1: |- X = U. J

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint X j
  disjoint X n
  assert |- ( J e. Top -> ( limPt ` J ) = ( x e. ~P X |-> { y | y e. ( ( cls ` J ) ` ( x \ { y } ) ) } ) )

  proof
    cJ
    ctop
    wcel
    #
    vx
    cX
    cpw
    #
    vy
    cv
    #
    vx
    cv
    @2
    csn
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    vy
    cab
    #
    cmpt
    #
    cvv
    wcel
    #
    cJ
    clp
    cfv
    @8
    wceq
    @0
    cX
    cJ
    wcel
    @1
    cvv
    wcel
    @9
    cJ
    cX
    lpfval.1
    topopn
    cX
    cJ
    pwexg
    vx
    @1
    @7
    cvv
    mptexg
    3syl
    vj
    cJ
    vx
    vj
    cv
    #
    cuni
    #
    cpw
    #
    @2
    @3
    @10
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    vy
    cab
    #
    cmpt
    @8
    ctop
    cvv
    clp
    @10
    cJ
    wceq
    #
    vx
    @12
    @16
    @1
    @7
    @17
    @11
    cX
    @17
    @11
    cJ
    cuni
    cX
    @10
    cJ
    unieq
    lpfval.1
    syl6eqr
    pweqd
    @17
    @15
    @6
    vy
    @17
    @14
    @5
    @2
    @17
    @3
    @13
    @4
    @10
    cJ
    ccl
    fveq2
    fveq1d
    eleq2d
    abbidv
    mpteq12dv
    vx
    vy
    vj
    df-lp
    fvmptg
    mpdan
end
