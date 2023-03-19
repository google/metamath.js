include "c0.mm"
include "cun.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"

theorem 0un
  let cA: class A


  assert |- ( (/) u. A ) = A

  proof
    c0
    cA
    cun
    cA
    c0
    cun
    cA
    c0
    cA
    uncom
    cA
    un0
    eqtri
end
