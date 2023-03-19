include "wss.mm"
include "cin.mm"
include "ssinss1.mm"
include "incom.mm"
include "syl5eqss.mm"
include "jaoi.mm"

theorem inss
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C \/ B C_ C ) -> ( A i^i B ) C_ C )

  proof
    cA
    cC
    wss
    cA
    cB
    cin
    #
    cC
    wss
    cB
    cC
    wss
    #
    cA
    cB
    cC
    ssinss1
    @1
    @0
    cB
    cA
    cin
    cC
    cA
    cB
    incom
    cB
    cA
    cC
    ssinss1
    syl5eqss
    jaoi
end
