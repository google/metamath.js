include "cmpt.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cop.mm"
include "dfmpt3.mm"
include "wceq.mm"
include "wcel.mm"
include "vex.mm"
include "xpsn.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "eqtri.mm"

theorem dfmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume dfmpt.1: |- B e. _V


  assert |- ( x e. A |-> B ) = U_ x e. A { <. x , B >. }

  proof
    vx
    cA
    cB
    cmpt
    vx
    cA
    vx
    cv
    #
    csn
    cB
    csn
    cxp
    #
    ciun
    vx
    cA
    @0
    cB
    cop
    csn
    #
    ciun
    vx
    cA
    cB
    dfmpt3
    vx
    cA
    @1
    @2
    @1
    @2
    wceq
    @0
    cA
    wcel
    @0
    cB
    vx
    vex
    dfmpt.1
    xpsn
    a1i
    iuneq2i
    eqtri
end
