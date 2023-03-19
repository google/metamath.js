include "c0.mm"
include "wne.mm"
include "wtr.mm"
include "cint.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "intss1.mm"
include "trss.mm"
include "com12.mm"
include "sstr2.mm"
include "sylsyld.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "impcom.mm"

theorem trintss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( Tr A /\ A =/= (/) ) -> |^| A C_ A )

  proof
    cA
    c0
    wne
    #
    cA
    wtr
    #
    cA
    cint
    #
    cA
    wss
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
    @1
    @3
    wi
    #
    vx
    cA
    n0
    @5
    @6
    vx
    @5
    @2
    @4
    wss
    @1
    @4
    cA
    wss
    #
    @3
    @4
    cA
    intss1
    @1
    @5
    @7
    cA
    @4
    trss
    com12
    @2
    @4
    cA
    sstr2
    sylsyld
    exlimiv
    sylbi
    impcom
end
