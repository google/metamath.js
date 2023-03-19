include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "brsdom.mm"
include "simprbi.mm"

theorem sdomnen
  let cA: class A
  let cB: class B


  assert |- ( A ~< B -> -. A ~~ B )

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
    simprbi
end
