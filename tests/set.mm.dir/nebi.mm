include "wceq.mm"
include "wb.mm"
include "wne.mm"
include "id.mm"
include "necon3bid.mm"
include "necon4bid.mm"
include "impbii.mm"

theorem nebi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B <-> C = D ) <-> ( A =/= B <-> C =/= D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    wb
    #
    cA
    cB
    wne
    cC
    cD
    wne
    wb
    #
    @0
    cA
    cB
    cC
    cD
    @0
    id
    necon3bid
    @1
    cA
    cB
    cC
    cD
    @1
    id
    necon4bid
    impbii
end
