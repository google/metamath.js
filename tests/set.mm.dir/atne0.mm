include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "c0h.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "elat2.mm"
include "simprl.mm"
include "sylbi.mm"

theorem atne0
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- ( A e. HAtoms -> A =/= 0H )

  proof
    cA
    cat
    wcel
    cA
    cch
    wcel
    #
    cA
    c0h
    wne
    #
    vx
    cv
    #
    cA
    wss
    @2
    cA
    wceq
    @2
    c0h
    wceq
    wo
    wi
    vx
    cch
    wral
    #
    wa
    wa
    @1
    vx
    cA
    elat2
    @0
    @1
    @3
    simprl
    sylbi
end
