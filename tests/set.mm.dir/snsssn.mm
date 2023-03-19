include "csn.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "sssn.mm"
include "snnz.mm"
include "neii.mm"
include "pm2.21i.mm"
include "sneqr.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem snsssn
  let cA: class A
  let cB: class B
  assume sneqr.1: |- A e. _V


  assert |- ( { A } C_ { B } -> A = B )

  proof
    cA
    csn
    #
    cB
    csn
    #
    wss
    @0
    c0
    wceq
    #
    @0
    @1
    wceq
    #
    wo
    cA
    cB
    wceq
    #
    @0
    cB
    sssn
    @2
    @4
    @3
    @2
    @4
    @0
    c0
    cA
    sneqr.1
    snnz
    neii
    pm2.21i
    cA
    cB
    sneqr.1
    sneqr
    jaoi
    sylbi
end
