include "wceq.mm"
include "co.mm"
include "oveq1.mm"
include "ax-mp.mm"

theorem oveq1i
  param cA: class A
  param cB: class B
  param cC: class C
  param cF: class F
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
