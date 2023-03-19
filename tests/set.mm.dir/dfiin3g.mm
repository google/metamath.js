include "wcel.mm"
include "wral.mm"
include "ciin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "cmpt.mm"
include "crn.mm"
include "dfiin2g.mm"
include "eqid.mm"
include "rnmpt.mm"
include "inteqi.mm"
include "syl6eqr.mm"

theorem dfiin3g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A. x e. A B e. C -> |^|_ x e. A B = |^| ran ( x e. A |-> B ) )

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
    ciin
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
    cint
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cint
    vx
    vy
    cA
    cB
    cC
    dfiin2g
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
    inteqi
    syl6eqr
end
