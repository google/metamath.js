include "cv.mm"
include "wss.mm"
include "cdif.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "wa.mm"
include "wceq.mm"
include "uniss2.mm"
include "difss.mm"
include "unissi.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"

theorem unidif
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( A. x e. A E. y e. ( A \ B ) x C_ y -> U. ( A \ B ) = U. A )

  proof
    vx
    cv
    vy
    cv
    wss
    vy
    cA
    cB
    cdif
    #
    wrex
    vx
    cA
    wral
    #
    @0
    cuni
    #
    cA
    cuni
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    @2
    @3
    wceq
    @1
    @5
    @4
    vx
    vy
    cA
    @0
    uniss2
    @0
    cA
    cA
    cB
    difss
    unissi
    jctil
    @2
    @3
    eqss
    sylibr
end
