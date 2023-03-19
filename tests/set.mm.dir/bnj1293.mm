include "cin.mm"
include "inss2.mm"
include "eqsstri.mm"

theorem bnj1293
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj1293.1: |- A = ( B i^i C )


  assert |- A C_ C

  proof
    cA
    cB
    cC
    cin
    cC
    bnj1293.1
    cB
    cC
    inss2
    eqsstri
end
