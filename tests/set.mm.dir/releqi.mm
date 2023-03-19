include "wceq.mm"
include "wrel.mm"
include "wb.mm"
include "releq.mm"
include "ax-mp.mm"

theorem releqi
  let cA: class A
  let cB: class B
  assume releqi.1: |- A = B


  assert |- ( Rel A <-> Rel B )

  proof
    cA
    cB
    wceq
    cA
    wrel
    cB
    wrel
    wb
    releqi.1
    cA
    cB
    releq
    ax-mp
end
