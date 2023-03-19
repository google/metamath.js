include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "ccld.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "cvv.mm"
include "ccl.mm"
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
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "df-cls.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem clsfval
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume cldval.1: |- X = U. J

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint X j
  assert |- ( J e. Top -> ( cls ` J ) = ( x e. ~P X |-> |^| { y e. ( Clsd ` J ) | x C_ y } ) )

  proof
    cJ
    ctop
    wcel
    #
    vx
    cX
    cpw
    #
    vx
    cv
    vy
    cv
    wss
    #
    vy
    cJ
    ccld
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    #
    cvv
    wcel
    #
    cJ
    ccl
    cfv
    @6
    wceq
    @0
    cX
    cJ
    wcel
    @1
    cvv
    wcel
    @7
    cJ
    cX
    cldval.1
    topopn
    cX
    cJ
    pwexg
    vx
    @1
    @5
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
    vy
    @8
    ccld
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    @6
    ctop
    cvv
    ccl
    @8
    cJ
    wceq
    #
    vx
    @10
    @13
    @1
    @5
    @14
    @9
    cX
    @14
    @9
    cJ
    cuni
    cX
    @8
    cJ
    unieq
    cldval.1
    syl6eqr
    pweqd
    @14
    @12
    @4
    @14
    @11
    @3
    wceq
    @12
    @4
    wceq
    @8
    cJ
    ccld
    fveq2
    @2
    vy
    @11
    @3
    rabeq
    syl
    inteqd
    mpteq12dv
    vx
    vy
    vj
    df-cls
    fvmptg
    mpdan
end
