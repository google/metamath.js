include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "eleq2.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem nelne1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ -. A e. C ) -> B =/= C )

  proof
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wn
    cB
    cC
    wne
    @0
    @1
    cB
    cC
    cB
    cC
    wceq
    @0
    @1
    cB
    cC
    cA
    eleq2
    biimpcd
    necon3bd
    imp
end
