include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wss.mm"
include "intss1.mm"
include "vex.mm"
include "ssex.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "wceq.mm"
include "vprc.mm"
include "inteq.mm"
include "int0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "impbii.mm"

theorem intex
  let cA: class A
  let vx: setvar x


  assert |- ( A =/= (/) <-> |^| A e. _V )

  proof
    cA
    c0
    wne
    #
    cA
    cint
    #
    cvv
    wcel
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    @2
    vx
    cA
    n0
    @4
    @2
    vx
    @4
    @1
    @3
    wss
    @2
    @3
    cA
    intss1
    @1
    @3
    vx
    vex
    ssex
    syl
    exlimiv
    sylbi
    @2
    cA
    c0
    cA
    c0
    wceq
    #
    @2
    cvv
    cvv
    wcel
    vprc
    @5
    @1
    cvv
    cvv
    @5
    @1
    c0
    cint
    cvv
    cA
    c0
    inteq
    int0
    syl6eq
    eleq1d
    mtbiri
    necon2ai
    impbii
end
