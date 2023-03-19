include "wcel.mm"
include "wo.mm"
include "bnj1138.mm"
include "biimpi.mm"

theorem bnj1424
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume bnj1424.1: |- A = ( B u. C )


  assert |- ( D e. A -> ( D e. B \/ D e. C ) )

  proof
    cD
    cA
    wcel
    cD
    cB
    wcel
    cD
    cC
    wcel
    wo
    cA
    cB
    cC
    cD
    bnj1424.1
    bnj1138
    biimpi
end
