include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "sdomdom.mm"
include "domsdomtr.mm"
include "sylan.mm"

theorem sdomtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~< B /\ B ~< C ) -> A ~< C )

  proof
    cA
    cB
    csdm
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
    sdomdom
    cA
    cB
    cC
    domsdomtr
    sylan
end
