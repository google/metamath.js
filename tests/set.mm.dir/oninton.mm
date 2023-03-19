include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wcel.mm"
include "onint.mm"
include "ex.mm"
include "ssel.mm"
include "syld.mm"
include "imp.mm"

theorem oninton
  let cA: class A


  assert |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. On )

  proof
    cA
    con0
    wss
    #
    cA
    c0
    wne
    #
    cA
    cint
    #
    con0
    wcel
    #
    @0
    @1
    @2
    cA
    wcel
    #
    @3
    @0
    @1
    @4
    cA
    onint
    ex
    cA
    con0
    @2
    ssel
    syld
    imp
end
