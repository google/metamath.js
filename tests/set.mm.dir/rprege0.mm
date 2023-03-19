include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "rpre.mm"
include "rpge0.mm"
include "jca.mm"

theorem rprege0
  let cA: class A


  assert |- ( A e. RR+ -> ( A e. RR /\ 0 <_ A ) )

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    rpre
    cA
    rpge0
    jca
end
