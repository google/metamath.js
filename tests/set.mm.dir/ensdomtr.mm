include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "csdm.mm"
include "endom.mm"
include "domsdomtr.mm"
include "sylan.mm"

theorem ensdomtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~~ B /\ B ~< C ) -> A ~< C )

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
    csdm
    wbr
    cA
    cC
    csdm
    wbr
    cA
    cB
    endom
    cA
    cB
    cC
    domsdomtr
    sylan
end
