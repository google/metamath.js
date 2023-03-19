include "cin.mm"
include "inss1.mm"
include "eqsstri.mm"

theorem bnj1292
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj1292.1: |- A = ( B i^i C )


  assert |- A C_ B

  proof
    cA
    cB
    cC
    cin
    cB
    bnj1292.1
    cB
    cC
    inss1
    eqsstri
end
