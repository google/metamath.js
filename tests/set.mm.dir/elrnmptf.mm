include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "nfcv.mm"
include "nfeq.mm"
include "eqeq1.mm"
include "rexbid.mm"
include "rnmpt.mm"
include "elab2g.mm"

theorem elrnmptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vy: setvar y
  assume elrnmptf.1: |- F/_ x C
  assume elrnmptf.2: |- F = ( x e. A |-> B )


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
    vx
    @0
    cC
    vx
    @0
    nfcv
    elrnmptf.1
    nfeq
    @0
    cC
    cB
    eqeq1
    rexbid
    vx
    vy
    cA
    cB
    cF
    elrnmptf.2
    rnmpt
    elab2g
end
