include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cxdiv.mm"
include "co.mm"
include "wceq.mm"
include "rprene0.mm"
include "xdiv0.mm"
include "syl.mm"

theorem xdiv0rp
  let cA: class A


  assert |- ( A e. RR+ -> ( 0 /e A ) = 0 )

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
    wa
    cc0
    cA
    cxdiv
    co
    cc0
    wceq
    cA
    rprene0
    cA
    xdiv0
    syl
end
