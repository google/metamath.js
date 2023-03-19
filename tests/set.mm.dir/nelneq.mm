include "wcel.mm"
include "wceq.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "con3dimp.mm"

theorem nelneq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ -. B e. C ) -> -. A = B )

  proof
    cA
    cC
    wcel
    #
    cA
    cB
    wceq
    #
    cB
    cC
    wcel
    #
    @1
    @0
    @2
    cA
    cB
    cC
    eleq1
    biimpcd
    con3dimp
end
