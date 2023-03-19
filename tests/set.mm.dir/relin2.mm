include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wi.mm"
include "inss2.mm"
include "relss.mm"
include "ax-mp.mm"

theorem relin2
  let cA: class A
  let cB: class B


  assert |- ( Rel B -> Rel ( A i^i B ) )

  proof
    cA
    cB
    cin
    #
    cB
    wss
    cB
    wrel
    @0
    wrel
    wi
    cA
    cB
    inss2
    @0
    cB
    relss
    ax-mp
end
