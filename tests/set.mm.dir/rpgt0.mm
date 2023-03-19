include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "elrp.mm"
include "simprbi.mm"

theorem rpgt0
  let cA: class A


  assert |- ( A e. RR+ -> 0 < A )

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    elrp
    simprbi
end
