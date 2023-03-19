include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "rpre.mm"
include "rpne0.mm"
include "jca.mm"

theorem rprene0
  let cA: class A


  assert |- ( A e. RR+ -> ( A e. RR /\ A =/= 0 ) )

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    cA
    cc0
    wne
    cA
    rpre
    cA
    rpne0
    jca
end
