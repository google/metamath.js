include "cr.mm"
include "cxr.mm"
include "ressxr.mm"
include "sseli.mm"

theorem rexr
  let cA: class A


  assert |- ( A e. RR -> A e. RR* )

  proof
    cr
    cxr
    cA
    ressxr
    sseli
end
