include "cvv.mm"
include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "vex.mm"
include "biantrur.mm"
include "opabbii.mm"
include "eqtr4i.mm"

theorem mptv
  let vx: setvar x
  let vy: setvar y
  let cB: class B

  disjoint x y
  disjoint B y
  assert |- ( x e. _V |-> B ) = { <. x , y >. | y = B }

  proof
    vx
    cvv
    cB
    cmpt
    vx
    cv
    cvv
    wcel
    #
    vy
    cv
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    @1
    vx
    vy
    copab
    vx
    vy
    cvv
    cB
    df-mpt
    @1
    @2
    vx
    vy
    @0
    @1
    vx
    vex
    biantrur
    opabbii
    eqtr4i
end
