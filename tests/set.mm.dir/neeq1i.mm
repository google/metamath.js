include "eqeq1i.mm"
include "necon3bii.mm"

theorem neeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume neeq1i.1: |- A = B


  assert |- ( A =/= C <-> B =/= C )

  proof
    cA
    cC
    cB
    cC
    cA
    cB
    cC
    neeq1i.1
    eqeq1i
    necon3bii
end
