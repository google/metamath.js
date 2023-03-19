include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "wceq.mm"
include "cnvss.mm"
include "anim12i.mm"
include "eqss.mm"
include "3imtr4i.mm"

theorem cnveq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> `' A = `' B )

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
    ccnv
    #
    cB
    ccnv
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
    cnvss
    cB
    cA
    cnvss
    anim12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3imtr4i
end
