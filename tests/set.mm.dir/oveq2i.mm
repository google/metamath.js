include "wceq.mm"
include "co.mm"
include "oveq2.mm"
include "ax-mp.mm"

theorem oveq2i
  param cA: class A
  param cB: class B
  param cC: class C
  param cF: class F
  assume oveq1i.1: |- A = B


  assert |- ( C F A ) = ( C F B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cF
    co
    cC
    cB
    cF
    co
    wceq
    oveq1i.1
    cA
    cB
    cC
    cF
    oveq2
    ax-mp
end
