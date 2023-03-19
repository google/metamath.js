include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "opth.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "anidm.mm"
include "3bitri.mm"

theorem opcom
  let cA: class A
  let cB: class B
  assume opcom.1: |- A e. _V
  assume opcom.2: |- B e. _V


  assert |- ( <. A , B >. = <. B , A >. <-> A = B )

  proof
    cA
    cB
    cop
    cB
    cA
    cop
    wceq
    cA
    cB
    wceq
    #
    cB
    cA
    wceq
    #
    wa
    @0
    @0
    wa
    @0
    cA
    cB
    cB
    cA
    opcom.1
    opcom.2
    opth
    @1
    @0
    @0
    cB
    cA
    eqcom
    anbi2i
    @0
    anidm
    3bitri
end
