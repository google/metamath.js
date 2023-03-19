include "eqeq2i.mm"
include "necon3bii.mm"

theorem neeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume neeq1i.1: |- A = B


  assert |- ( C =/= A <-> C =/= B )

  proof
    cC
    cA
    cC
    cB
    cA
    cB
    cC
    neeq1i.1
    eqeq2i
    necon3bii
end
