include "wcel.mm"
include "wceq.mm"
include "eleq2.mm"
include "biimpcd.mm"
include "con3dimp.mm"

theorem nelneq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ -. A e. C ) -> -. B = C )

  proof
    cA
    cB
    wcel
    #
    cB
    cC
    wceq
    #
    cA
    cC
    wcel
    #
    @1
    @0
    @2
    cB
    cC
    cA
    eleq2
    biimpcd
    con3dimp
end
