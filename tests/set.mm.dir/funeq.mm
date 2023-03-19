include "wceq.mm"
include "wfun.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "funss.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem funeq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( Fun A <-> Fun B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    wfun
    #
    cB
    wfun
    #
    @0
    cB
    cA
    wss
    @1
    @2
    wi
    cB
    cA
    eqimss2
    cB
    cA
    funss
    syl
    @0
    cA
    cB
    wss
    @2
    @1
    wi
    cA
    cB
    eqimss
    cA
    cB
    funss
    syl
    impbid
end
