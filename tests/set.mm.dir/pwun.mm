include "cun.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "wo.mm"
include "wceq.mm"
include "pwunss.mm"
include "biantru.mm"
include "pwssun.mm"
include "eqss.mm"
include "3bitr4i.mm"

theorem pwun
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B \/ B C_ A ) <-> ~P ( A u. B ) = ( ~P A u. ~P B ) )

  proof
    cA
    cB
    cun
    cpw
    #
    cA
    cpw
    cB
    cpw
    cun
    #
    wss
    #
    @2
    @1
    @0
    wss
    #
    wa
    cA
    cB
    wss
    cB
    cA
    wss
    wo
    @0
    @1
    wceq
    @3
    @2
    cA
    cB
    pwunss
    biantru
    cA
    cB
    pwssun
    @0
    @1
    eqss
    3bitr4i
end
