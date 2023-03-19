include "cop.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "cdm.mm"
include "wceq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "spcev.mm"
include "eldm2.mm"
include "sylibr.mm"

theorem opeldm
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume opeldm.1: |- A e. _V
  assume opeldm.2: |- B e. _V


  assert |- ( <. A , B >. e. C -> A e. dom C )

  proof
    cA
    cB
    cop
    #
    cC
    wcel
    #
    cA
    vy
    cv
    #
    cop
    #
    cC
    wcel
    #
    vy
    wex
    cA
    cC
    cdm
    wcel
    @4
    @1
    vy
    cB
    opeldm.2
    @2
    cB
    wceq
    @3
    @0
    cC
    @2
    cB
    cA
    opeq2
    eleq1d
    spcev
    vy
    cA
    cC
    opeldm.1
    eldm2
    sylibr
end
