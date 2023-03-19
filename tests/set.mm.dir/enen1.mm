include "cen.mm"
include "wbr.mm"
include "ensym.mm"
include "entr.mm"
include "sylan.mm"
include "impbida.mm"

theorem enen1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~~ B -> ( A ~~ C <-> B ~~ C ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cC
    cen
    wbr
    #
    cB
    cC
    cen
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
    entr
    sylan
    cA
    cB
    cC
    entr
    impbida
end
