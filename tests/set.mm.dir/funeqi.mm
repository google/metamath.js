include "wceq.mm"
include "wfun.mm"
include "wb.mm"
include "funeq.mm"
include "ax-mp.mm"

theorem funeqi
  let cA: class A
  let cB: class B
  assume funeqi.1: |- A = B


  assert |- ( Fun A <-> Fun B )

  proof
    cA
    cB
    wceq
    cA
    wfun
    cB
    wfun
    wb
    funeqi.1
    cA
    cB
    funeq
    ax-mp
end
