include "cvv.mm"
include "wcel.mm"
include "cssr.mm"
include "wbr.mm"
include "brssrid.mm"
include "wrel.mm"
include "relssr.mm"
include "brrelex.mm"
include "mpan.mm"
include "impbii.mm"

theorem issetssr
  let cA: class A


  assert |- ( A e. _V <-> A _S A )

  proof
    cA
    cvv
    wcel
    #
    cA
    cA
    cssr
    wbr
    #
    cA
    cvv
    brssrid
    cssr
    wrel
    @1
    @0
    relssr
    cA
    cA
    cssr
    brrelex
    mpan
    impbii
end
