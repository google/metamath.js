include "csn.mm"
include "cuni.mm"
include "cpr.mm"
include "cun.mm"
include "dfsn2.mm"
include "unieqi.mm"
include "unipr.mm"
include "unidm.mm"
include "3eqtri.mm"

theorem unisn
  let cA: class A
  assume unisn.1: |- A e. _V


  assert |- U. { A } = A

  proof
    cA
    csn
    #
    cuni
    cA
    cA
    cpr
    #
    cuni
    cA
    cA
    cun
    cA
    @0
    @1
    cA
    dfsn2
    unieqi
    cA
    cA
    unisn.1
    unisn.1
    unipr
    cA
    unidm
    3eqtri
end
