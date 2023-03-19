include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "wf.mm"
include "dffo3f.mm"
include "simprbi.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem foelrnf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  assume foelrnf.1: |- F/_ x F

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint F y
  assert |- ( ( F : A -onto-> B /\ C e. B ) -> E. x e. A C = ( F ` x ) )

  proof
    cA
    cB
    cF
    wfo
    #
    vy
    cv
    #
    vx
    cv
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    cC
    cB
    wcel
    cC
    @2
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    cA
    cB
    cF
    wf
    @5
    vx
    vy
    cA
    cB
    cF
    foelrnf.1
    dffo3f
    simprbi
    @4
    @7
    vy
    cC
    cB
    @1
    cC
    wceq
    @3
    @6
    vx
    cA
    @1
    cC
    @2
    eqeq1
    rexbidv
    rspccva
    sylan
end
