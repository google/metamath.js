include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "cspn.mm"
include "cfv.mm"
include "snssi.mm"
include "elspancl.mm"
include "sylan.mm"

theorem elspansncl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ( span ` { A } ) ) -> B e. ~H )

  proof
    cA
    chil
    wcel
    cA
    csn
    #
    chil
    wss
    cB
    @0
    cspn
    cfv
    wcel
    cB
    chil
    wcel
    cA
    chil
    snssi
    @0
    cB
    elspancl
    sylan
end
