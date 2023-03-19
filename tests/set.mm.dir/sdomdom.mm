include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "brsdom.mm"
include "simplbi.mm"

theorem sdomdom
  let cA: class A
  let cB: class B


  assert |- ( A ~< B -> A ~<_ B )

  proof
    cA
    cB
    csdm
    wbr
    cA
    cB
    cdom
    wbr
    cA
    cB
    cen
    wbr
    wn
    cA
    cB
    brsdom
    simplbi
end
