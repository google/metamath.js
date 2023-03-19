include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "pr1eqbg.mm"
include "necon3bid.mm"

theorem pr1nebg
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let cX: class X


  assert |- ( ( ( A e. U /\ B e. V /\ C e. X ) /\ A =/= B ) -> ( A =/= C <-> { A , B } =/= { B , C } ) )

  proof
    cA
    cU
    wcel
    cB
    cV
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    wne
    wa
    cA
    cC
    cA
    cB
    cpr
    cB
    cC
    cpr
    cA
    cB
    cC
    cU
    cV
    cX
    pr1eqbg
    necon3bid
end
