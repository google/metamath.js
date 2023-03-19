include "cn0.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "cr.mm"
include "pnfnre.mm"
include "neli.mm"
include "nn0re.mm"
include "mto.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"

theorem nn0nepnf
  let cA: class A


  assert |- ( A e. NN0 -> A =/= +oo )

  proof
    cA
    cn0
    wcel
    #
    cA
    cpnf
    cA
    cpnf
    wceq
    @0
    cpnf
    cn0
    wcel
    #
    @1
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    cpnf
    nn0re
    mto
    cA
    cpnf
    cn0
    eleq1
    mtbiri
    necon2ai
end
