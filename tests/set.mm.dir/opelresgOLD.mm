include "cv.mm"
include "cop.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "anbi1d.mm"
include "vex.mm"
include "opelres.mm"
include "vtoclbg.mm"

theorem opelresgOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vy: setvar y


  assert |- ( B e. V -> ( <. A , B >. e. ( C |` D ) <-> ( <. A , B >. e. C /\ A e. D ) ) )

  proof
    cA
    vy
    cv
    #
    cop
    #
    cC
    cD
    cres
    #
    wcel
    @1
    cC
    wcel
    #
    cA
    cD
    wcel
    #
    wa
    cA
    cB
    cop
    #
    @2
    wcel
    @5
    cC
    wcel
    #
    @4
    wa
    vy
    cB
    cV
    @0
    cB
    wceq
    #
    @1
    @5
    @2
    @0
    cB
    cA
    opeq2
    #
    eleq1d
    @7
    @3
    @6
    @4
    @7
    @1
    @5
    cC
    @8
    eleq1d
    anbi1d
    cA
    @0
    cC
    cD
    vy
    vex
    opelres
    vtoclbg
end
