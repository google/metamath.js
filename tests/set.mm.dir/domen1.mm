include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "ensym.mm"
include "endomtr.mm"
include "sylan.mm"
include "impbida.mm"

theorem domen1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~~ B -> ( A ~<_ C <-> B ~<_ C ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cC
    cdom
    wbr
    #
    cB
    cC
    cdom
    wbr
    #
    @0
    cB
    cA
    cen
    wbr
    @1
    @2
    cA
    cB
    ensym
    cB
    cA
    cC
    endomtr
    sylan
    cA
    cB
    cC
    endomtr
    impbida
end
