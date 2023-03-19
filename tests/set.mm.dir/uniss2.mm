include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "wcel.mm"
include "ssuni.mm"
include "expcom.mm"
include "rexlimiv.mm"
include "ralimi.mm"
include "unissb.mm"
include "sylibr.mm"

theorem uniss2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( A. x e. A E. y e. B x C_ y -> U. A C_ U. B )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    @0
    cB
    cuni
    #
    wss
    #
    vx
    cA
    wral
    cA
    cuni
    @4
    wss
    @3
    @5
    vx
    cA
    @2
    @5
    vy
    cB
    @2
    @1
    cB
    wcel
    @5
    @0
    @1
    cB
    ssuni
    expcom
    rexlimiv
    ralimi
    vx
    cA
    @4
    unissb
    sylibr
end
