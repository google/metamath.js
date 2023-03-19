include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "ssrin.mm"
include "eqimss.mm"
include "sylan9ss.mm"
include "ss0.mm"
include "syl.mm"

theorem ssdisj
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B /\ ( B i^i C ) = (/) ) -> ( A i^i C ) = (/) )

  proof
    cA
    cB
    wss
    #
    cB
    cC
    cin
    #
    c0
    wceq
    #
    wa
    cA
    cC
    cin
    #
    c0
    wss
    @3
    c0
    wceq
    @0
    @2
    @3
    @1
    c0
    cA
    cB
    cC
    ssrin
    @1
    c0
    eqimss
    sylan9ss
    @3
    ss0
    syl
end
