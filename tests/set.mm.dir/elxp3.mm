include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elxp.mm"
include "eqcom.mm"
include "opelxp.mm"
include "anbi12i.mm"
include "2exbii.mm"
include "bitr4i.mm"

theorem elxp3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( A e. ( B X. C ) <-> E. x E. y ( <. x , y >. = A /\ <. x , y >. e. ( B X. C ) ) )

  proof
    cA
    cB
    cC
    cxp
    #
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @1
    cB
    wcel
    @2
    cC
    wcel
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    @3
    cA
    wceq
    #
    @3
    @0
    wcel
    #
    wa
    #
    vy
    wex
    vx
    wex
    vx
    vy
    cA
    cB
    cC
    elxp
    @9
    @6
    vx
    vy
    @7
    @4
    @8
    @5
    @3
    cA
    eqcom
    @1
    @2
    cB
    cC
    opelxp
    anbi12i
    2exbii
    bitr4i
end
