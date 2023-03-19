include "wse.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "df-se.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylanb.mm"

theorem seex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let vy: setvar y
  let vz: setvar z
  let cV: class V

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint V x
  disjoint V y
  assert |- ( ( R Se A /\ B e. A ) -> { x e. A | x R B } e. _V )

  proof
    cA
    cR
    wse
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    cA
    crab
    #
    cvv
    wcel
    #
    vy
    cA
    wral
    cB
    cA
    wcel
    @0
    cB
    cR
    wbr
    #
    vx
    cA
    crab
    #
    cvv
    wcel
    #
    vy
    vx
    cA
    cR
    df-se
    @4
    @7
    vy
    cB
    cA
    @1
    cB
    wceq
    #
    @3
    @6
    cvv
    @8
    @2
    @5
    vx
    cA
    @1
    cB
    @0
    cR
    breq2
    rabbidv
    eleq1d
    rspccva
    sylanb
end
