include "wss.mm"
include "cvv.mm"
include "wnel.mm"
include "wcel.mm"
include "ssexg.mm"
include "ex.mm"
include "nelcon3d.mm"
include "imp.mm"

theorem prcssprc
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B /\ A e/ _V ) -> B e/ _V )

  proof
    cA
    cB
    wss
    #
    cA
    cvv
    wnel
    cB
    cvv
    wnel
    @0
    cB
    cvv
    cA
    cvv
    @0
    cB
    cvv
    wcel
    cA
    cvv
    wcel
    cA
    cB
    cvv
    ssexg
    ex
    nelcon3d
    imp
end
