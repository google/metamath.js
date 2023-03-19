include "wcel.mm"
include "wss.mm"
include "ssel.mm"
include "com12.mm"
include "con3dimp.mm"

theorem nelss
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ -. A e. C ) -> -. B C_ C )

  proof
    cA
    cB
    wcel
    #
    cB
    cC
    wss
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
    ssel
    com12
    con3dimp
end
