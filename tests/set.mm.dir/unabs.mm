include "cin.mm"
include "wss.mm"
include "cun.mm"
include "wceq.mm"
include "inss1.mm"
include "ssequn2.mm"
include "mpbi.mm"

theorem unabs
  let cA: class A
  let cB: class B


  assert |- ( A u. ( A i^i B ) ) = A

  proof
    cA
    cB
    cin
    #
    cA
    wss
    cA
    @0
    cun
    cA
    wceq
    cA
    cB
    inss1
    @0
    cA
    ssequn2
    mpbi
end
