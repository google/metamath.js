include "cdif.mm"
include "cun.mm"
include "undif3.mm"
include "unidm.mm"
include "difeq1i.mm"
include "difdif.mm"
include "3eqtri.mm"

theorem undifabs
  let cA: class A
  let cB: class B


  assert |- ( A u. ( A \ B ) ) = A

  proof
    cA
    cA
    cB
    cdif
    cun
    cA
    cA
    cun
    #
    cB
    cA
    cdif
    #
    cdif
    cA
    @1
    cdif
    cA
    cA
    cA
    cB
    undif3
    @0
    cA
    @1
    cA
    unidm
    difeq1i
    cA
    cB
    difdif
    3eqtri
end
