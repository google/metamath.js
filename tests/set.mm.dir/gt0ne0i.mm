include "cc0.mm"
include "0re.mm"
include "ltnei.mm"

theorem gt0ne0i
  let cA: class A
  assume lt2.1: |- A e. RR


  assert |- ( 0 < A -> A =/= 0 )

  proof
    cc0
    cA
    0re
    lt2.1
    ltnei
end
