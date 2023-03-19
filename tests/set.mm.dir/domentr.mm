include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "endom.mm"
include "domtr.mm"
include "sylan2.mm"

theorem domentr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~<_ B /\ B ~~ C ) -> A ~<_ C )

  proof
    cB
    cC
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
    cB
    cC
    endom
    cA
    cB
    cC
    domtr
    sylan2
end
