include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cxne.mm"
include "xnegrecl.mm"
include "adantl.mm"
include "xnegrecl2.mm"
include "impbida.mm"

theorem xnegre
  let cA: class A


  assert |- ( A e. RR* -> ( A e. RR <-> -e A e. RR ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cxne
    cr
    wcel
    #
    @1
    @2
    @0
    cA
    xnegrecl
    adantl
    cA
    xnegrecl2
    impbida
end
