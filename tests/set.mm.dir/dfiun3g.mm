include "wcel.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cmpt.mm"
include "crn.mm"
include "dfiun2g.mm"
include "eqid.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "syl6eqr.mm"

theorem dfiun3g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A. x e. A B e. C -> U_ x e. A B = U. ran ( x e. A |-> B ) )

  proof
    cB
    cC
    wcel
    vx
    cA
    wral
    vx
    cA
    cB
    ciun
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cuni
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cuni
    vx
    vy
    cA
    cB
    cC
    dfiun2g
    @2
    @0
    vx
    vy
    cA
    cB
    @1
    @1
    eqid
    rnmpt
    unieqi
    syl6eqr
end
