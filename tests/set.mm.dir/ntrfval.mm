include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "cin.mm"
include "cuni.mm"
include "cmpt.mm"
include "cvv.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "topopn.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "ineq1.mm"
include "unieqd.mm"
include "mpteq12dv.mm"
include "df-ntr.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem ntrfval
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vj: setvar j
  assume cldval.1: |- X = U. J

  disjoint J x
  disjoint X x
  disjoint x y
  disjoint j x
  disjoint j y
  disjoint J y
  disjoint J j
  disjoint X j
  assert |- ( J e. Top -> ( int ` J ) = ( x e. ~P X |-> U. ( J i^i ~P x ) ) )

  proof
    cJ
    ctop
    wcel
    #
    vx
    cX
    cpw
    #
    cJ
    vx
    cv
    cpw
    #
    cin
    #
    cuni
    #
    cmpt
    #
    cvv
    wcel
    #
    cJ
    cnt
    cfv
    @5
    wceq
    @0
    cX
    cJ
    wcel
    @1
    cvv
    wcel
    @6
    cJ
    cX
    cldval.1
    topopn
    cX
    cJ
    pwexg
    vx
    @1
    @4
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
    @7
    @2
    cin
    #
    cuni
    #
    cmpt
    @5
    ctop
    cvv
    cnt
    @7
    cJ
    wceq
    #
    vx
    @9
    @11
    @1
    @4
    @12
    @8
    cX
    @12
    @8
    cJ
    cuni
    cX
    @7
    cJ
    unieq
    cldval.1
    syl6eqr
    pweqd
    @12
    @10
    @3
    @7
    cJ
    @2
    ineq1
    unieqd
    mpteq12dv
    vx
    vj
    df-ntr
    fvmptg
    mpdan
end
