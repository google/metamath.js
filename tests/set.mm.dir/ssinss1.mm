include "cin.mm"
include "wss.mm"
include "wi.mm"
include "inss1.mm"
include "sstr2.mm"
include "ax-mp.mm"

theorem ssinss1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ C -> ( A i^i B ) C_ C )

  proof
    cA
    cB
    cin
    #
    cA
    wss
    cA
    cC
    wss
    @0
    cC
    wss
    wi
    cA
    cB
    inss1
    @0
    cA
    cC
    sstr2
    ax-mp
end
