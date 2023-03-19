include "cen.mm"
include "cdom.mm"
include "enssdom.mm"
include "ssbri.mm"

theorem endom
  let cA: class A
  let cB: class B


  assert |- ( A ~~ B -> A ~<_ B )

  proof
    cen
    cdom
    cA
    cB
    enssdom
    ssbri
end
