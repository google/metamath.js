include "cen.mm"
include "wbr.mm"
include "csdm.mm"
include "sdomentr.mm"
include "ancoms.mm"
include "ensym.mm"
include "sylan.mm"
include "impbida.mm"

theorem sdomen2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~~ B -> ( C ~< A <-> C ~< B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cA
    csdm
    wbr
    #
    cC
    cB
    csdm
    wbr
    #
    @1
    @0
    @2
    cC
    cA
    cB
    sdomentr
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
    sdomentr
    ancoms
    sylan
    impbida
end
