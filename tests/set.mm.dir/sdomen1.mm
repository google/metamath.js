include "cen.mm"
include "wbr.mm"
include "csdm.mm"
include "ensym.mm"
include "ensdomtr.mm"
include "sylan.mm"
include "impbida.mm"

theorem sdomen1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~~ B -> ( A ~< C <-> B ~< C ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cC
    csdm
    wbr
    #
    cB
    cC
    csdm
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
    ensdomtr
    sylan
    cA
    cB
    cC
    ensdomtr
    impbida
end
