include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "cdif.mm"
include "wceq.mm"
include "complss.mm"
include "anbi12ci.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem compleq
  let cA: class A
  let cB: class B


  assert |- ( A = B <-> ( _V \ A ) = ( _V \ B ) )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    cvv
    cA
    cdif
    #
    cvv
    cB
    cdif
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    cA
    cB
    wceq
    @2
    @3
    wceq
    @0
    @5
    @1
    @4
    cA
    cB
    complss
    cB
    cA
    complss
    anbi12ci
    cA
    cB
    eqss
    @2
    @3
    eqss
    3bitr4i
end
