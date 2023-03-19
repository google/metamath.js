include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "elrp.mm"
include "biimpi.mm"

theorem rpregt0
  let cA: class A


  assert |- ( A e. RR+ -> ( A e. RR /\ 0 < A ) )

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
    wa
    cA
    elrp
    biimpi
end
