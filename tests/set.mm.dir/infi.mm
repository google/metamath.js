include "cfn.mm"
include "wcel.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "ssfi.mm"
include "mpan2.mm"

theorem infi
  let cA: class A
  let cB: class B


  assert |- ( A e. Fin -> ( A i^i B ) e. Fin )

  proof
    cA
    cfn
    wcel
    cA
    cB
    cin
    #
    cA
    wss
    @0
    cfn
    wcel
    cA
    cB
    inss1
    cA
    @0
    ssfi
    mpan2
end
