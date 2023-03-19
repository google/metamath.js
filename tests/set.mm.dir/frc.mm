include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fri.mm"
include "mpanl1.mm"
include "3impb.mm"
include "rabeq0.mm"
include "rexbii.mm"
include "sylibr.mm"

theorem frc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume frc.1: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( ( R Fr A /\ B C_ A /\ B =/= (/) ) -> E. x e. B { y e. B | y R x } = (/) )

  proof
    cA
    cR
    wfr
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    w3a
    vy
    cv
    vx
    cv
    cR
    wbr
    #
    wn
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @3
    vy
    cB
    crab
    c0
    wceq
    #
    vx
    cB
    wrex
    @0
    @1
    @2
    @5
    cB
    cvv
    wcel
    @0
    @1
    @2
    wa
    @5
    frc.1
    vx
    vy
    cA
    cB
    cvv
    cR
    fri
    mpanl1
    3impb
    @6
    @4
    vx
    cB
    @3
    vy
    cB
    rabeq0
    rexbii
    sylibr
end
