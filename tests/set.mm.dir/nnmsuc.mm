include "com.mm"
include "wcel.mm"
include "con0.mm"
include "csuc.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "nnon.mm"
include "onmsuc.mm"
include "sylan.mm"

theorem nnmsuc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A .o suc B ) = ( ( A .o B ) +o A ) )

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    cB
    com
    wcel
    cA
    cB
    csuc
    comu
    co
    cA
    cB
    comu
    co
    cA
    coa
    co
    wceq
    cA
    nnon
    cA
    cB
    onmsuc
    sylan
end
