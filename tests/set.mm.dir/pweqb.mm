include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wceq.mm"
include "sspwb.mm"
include "anbi12i.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem pweqb
  let cA: class A
  let cB: class B


  assert |- ( A = B <-> ~P A = ~P B )

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
    cA
    cpw
    #
    cB
    cpw
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
    @4
    @1
    @5
    cA
    cB
    sspwb
    cB
    cA
    sspwb
    anbi12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3bitr4i
end
