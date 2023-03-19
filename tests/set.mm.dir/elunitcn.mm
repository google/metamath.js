include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "elunitrn.mm"
include "recnd.mm"

theorem elunitcn
  let cA: class A


  assert |- ( A e. ( 0 [,] 1 ) -> A e. CC )

  proof
    cA
    cc0
    c1
    cicc
    co
    wcel
    cA
    cA
    elunitrn
    recnd
end
