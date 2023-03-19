include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "abbii.mm"
include "eqtr4i.mm"
include "dissneqlem.mm"

theorem dissneq
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  assume dissneq.c: |- C = { u | E. x e. A u = { x } }

  disjoint A u
  disjoint A x
  disjoint u x
  disjoint A z
  disjoint u z
  disjoint x z
  disjoint B z
  disjoint C z
  assert |- ( ( C C_ B /\ B e. ( TopOn ` A ) ) -> B = ~P A )

  proof
    vz
    vu
    cA
    cB
    cC
    cC
    vu
    cv
    #
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vu
    cab
    @0
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vu
    cab
    dissneq.c
    @8
    @4
    vu
    @7
    @3
    vz
    vx
    cA
    @5
    @1
    wceq
    @6
    @2
    @0
    @5
    @1
    sneq
    eqeq2d
    cbvrexv
    abbii
    eqtr4i
    dissneqlem
end
