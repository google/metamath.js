include "cen.mm"
include "wbr.mm"
include "entr.mm"
include "ancoms.mm"
include "ensym.mm"
include "sylan.mm"
include "impbida.mm"

theorem enen2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~~ B -> ( C ~~ A <-> C ~~ B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cA
    cen
    wbr
    #
    cC
    cB
    cen
    wbr
    #
    @1
    @0
    @2
    cC
    cA
    cB
    entr
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
    entr
    ancoms
    sylan
    impbida
end
