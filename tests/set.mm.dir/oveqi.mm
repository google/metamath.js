include "wceq.mm"
include "co.mm"
include "oveq.mm"
include "ax-mp.mm"

theorem oveqi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume oveq1i.1: |- A = B


  assert |- ( C A D ) = ( C B D )

  proof
    cA
    cB
    wceq
    cC
    cD
    cA
    co
    cC
    cD
    cB
    co
    wceq
    oveq1i.1
    cC
    cD
    cA
    cB
    oveq
    ax-mp
end
