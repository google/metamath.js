include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "endom.mm"
include "domtr.mm"
include "sylan.mm"

theorem endomtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~~ B /\ B ~<_ C ) -> A ~<_ C )

  proof
    cA
    cB
    cen
    wbr
    cA
    cB
    cdom
    wbr
    cB
    cC
    cdom
    wbr
    cA
    cC
    cdom
    wbr
    cA
    cB
    endom
    cA
    cB
    cC
    domtr
    sylan
end
