include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "cnei.mm"
include "cfv.mm"
include "wceq.mm"
include "topopn.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "cuni.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "rexeq.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-nei.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem neifval
  let vx: setvar x
  let vv: setvar v
  let vg: setvar g
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let cN: class N
  let cP: class P
  let cS: class S
  assume neifval.1: |- X = U. J

  disjoint g v
  disjoint g x
  disjoint J g
  disjoint v x
  disjoint J v
  disjoint J x
  disjoint X g
  disjoint X v
  disjoint X x
  disjoint g j
  disjoint j v
  disjoint j x
  disjoint J j
  disjoint N g
  disjoint N v
  disjoint P g
  disjoint S g
  disjoint S v
  disjoint S x
  disjoint X j
  assert |- ( J e. Top -> ( nei ` J ) = ( x e. ~P X |-> { v e. ~P X | E. g e. J ( x C_ g /\ g C_ v ) } ) )

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
    vg
    cv
    #
    wss
    @2
    vv
    cv
    wss
    wa
    #
    vg
    cJ
    wrex
    #
    vv
    @1
    crab
    #
    cmpt
    #
    cvv
    wcel
    #
    cJ
    cnei
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
    neifval.1
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
    @3
    vg
    @8
    wrex
    #
    vv
    @10
    crab
    #
    cmpt
    @6
    ctop
    cvv
    cnei
    @8
    cJ
    wceq
    #
    vx
    @10
    @12
    @1
    @5
    @13
    @9
    cX
    @13
    @9
    cJ
    cuni
    cX
    @8
    cJ
    unieq
    neifval.1
    syl6eqr
    pweqd
    #
    @13
    @11
    @4
    vv
    @10
    @1
    @14
    @3
    vg
    @8
    cJ
    rexeq
    rabeqbidv
    mpteq12dv
    vx
    vv
    vg
    vj
    df-nei
    fvmptg
    mpdan
end
