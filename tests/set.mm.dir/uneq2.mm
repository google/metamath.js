include "wceq.mm"
include "cun.mm"
include "uneq1.mm"
include "uncom.mm"
include "3eqtr4g.mm"

theorem uneq2
  param cA: class A
  param cB: class B
  param cC: class C


  assert |- ( A = B -> ( C u. A ) = ( C u. B ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    cun
    cB
    cC
    cun
    cC
    cA
    cun
    cC
    cB
    cun
    cA
    cB
    cC
    uneq1
    cC
    cA
    uncom
    cC
    cB
    uncom
    3eqtr4g
end
