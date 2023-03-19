include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wceq.mm"
include "mnfnre.mm"
include "neli.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"

theorem renemnf
  let cA: class A


  assert |- ( A e. RR -> A =/= -oo )

  proof
    cA
    cr
    wcel
    #
    cA
    cmnf
    cA
    cmnf
    wceq
    @0
    cmnf
    cr
    wcel
    cmnf
    cr
    mnfnre
    neli
    cA
    cmnf
    cr
    eleq1
    mtbiri
    necon2ai
end
