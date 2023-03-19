include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseli.mm"

theorem eliccxr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B [,] C ) -> A e. RR* )

  proof
    cB
    cC
    cicc
    co
    cxr
    cA
    cB
    cC
    iccssxr
    sseli
end
