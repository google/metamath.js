include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem nelne2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ -. B e. C ) -> A =/= B )

  proof
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    wn
    cA
    cB
    wne
    @0
    @1
    cA
    cB
    cA
    cB
    wceq
    @0
    @1
    cA
    cB
    cC
    eleq1
    biimpcd
    necon3bd
    imp
end
