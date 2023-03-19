include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "ss0b.mm"
include "wi.mm"
include "ssrin.mm"
include "sstr2.mm"
include "syl.mm"
include "syl5bir.mm"
include "imp.mm"
include "ss0.mm"

theorem ssdisjOLD
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
    #
    @3
    c0
    wceq
    @0
    @2
    @4
    @2
    @1
    c0
    wss
    #
    @0
    @4
    @1
    ss0b
    @0
    @3
    @1
    wss
    @5
    @4
    wi
    cA
    cB
    cC
    ssrin
    @3
    @1
    c0
    sstr2
    syl
    syl5bir
    imp
    @3
    ss0
    syl
end
