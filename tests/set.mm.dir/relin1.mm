include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wi.mm"
include "inss1.mm"
include "relss.mm"
include "ax-mp.mm"

theorem relin1
  let cA: class A
  let cB: class B


  assert |- ( Rel A -> Rel ( A i^i B ) )

  proof
    cA
    cB
    cin
    #
    cA
    wss
    cA
    wrel
    @0
    wrel
    wi
    cA
    cB
    inss1
    @0
    cA
    relss
    ax-mp
end
