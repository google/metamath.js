include "wceq.mm"
include "co.mm"
include "oveq1.mm"
include "ax-mp.mm"

theorem oveq1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume oveq1i.1: |- A = B


  assert |- ( A F C ) = ( B F C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cF
    co
    cB
    cC
    cF
    co
    wceq
    oveq1i.1
    cA
    cB
    cC
    cF
    oveq1
    ax-mp
end
