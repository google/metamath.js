include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "domentr.mm"
include "ancoms.mm"
include "ensym.mm"
include "sylan.mm"
include "impbida.mm"

theorem domen2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~~ B -> ( C ~<_ A <-> C ~<_ B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cA
    cdom
    wbr
    #
    cC
    cB
    cdom
    wbr
    #
    @1
    @0
    @2
    cC
    cA
    cB
    domentr
    ancoms
    @0
    cB
    cA
    cen
    wbr
    #
    @2
    @1
    cA
    cB
    ensym
    @2
    @3
    @1
    cC
    cB
    cA
    domentr
    ancoms
    sylan
    impbida
end
