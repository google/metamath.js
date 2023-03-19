include "wss.mm"
include "cun.mm"
include "wceq.mm"
include "cdif.mm"
include "ssequn1.mm"
include "undif2.mm"
include "eqeq1i.mm"
include "bitr4i.mm"

theorem undif
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( A u. ( B \ A ) ) = B )

  proof
    cA
    cB
    wss
    cA
    cB
    cun
    #
    cB
    wceq
    cA
    cB
    cA
    cdif
    cun
    #
    cB
    wceq
    cA
    cB
    ssequn1
    @1
    @0
    cB
    cA
    cB
    undif2
    eqeq1i
    bitr4i
end
