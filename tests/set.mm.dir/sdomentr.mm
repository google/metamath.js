include "cen.mm"
include "wbr.mm"
include "csdm.mm"
include "cdom.mm"
include "endom.mm"
include "sdomdomtr.mm"
include "sylan2.mm"

theorem sdomentr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~< B /\ B ~~ C ) -> A ~< C )

  proof
    cB
    cC
    cen
    wbr
    cA
    cB
    csdm
    wbr
    cB
    cC
    cdom
    wbr
    cA
    cC
    csdm
    wbr
    cB
    cC
    endom
    cA
    cB
    cC
    sdomdomtr
    sylan2
end
