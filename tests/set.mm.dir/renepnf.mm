include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "pnfnre.mm"
include "neli.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"

theorem renepnf
  let cA: class A


  assert |- ( A e. RR -> A =/= +oo )

  proof
    cA
    cr
    wcel
    #
    cA
    cpnf
    cA
    cpnf
    wceq
    @0
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    cA
    cpnf
    cr
    eleq1
    mtbiri
    necon2ai
end
