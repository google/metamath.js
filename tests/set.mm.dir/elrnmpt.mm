include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rnmpt.mm"
include "elab2g.mm"

theorem elrnmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume rnmpt.1: |- F = ( x e. A |-> B )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  assert |- ( C e. V -> ( C e. ran F <-> E. x e. A C = B ) )

  proof
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    cC
    cB
    wceq
    #
    vx
    cA
    wrex
    vy
    cC
    cF
    crn
    cV
    @0
    cC
    wceq
    @1
    @2
    vx
    cA
    @0
    cC
    cB
    eqeq1
    rexbidv
    vx
    vy
    cA
    cB
    cF
    rnmpt.1
    rnmpt
    elab2g
end
