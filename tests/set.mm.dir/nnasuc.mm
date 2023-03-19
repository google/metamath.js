include "com.mm"
include "wcel.mm"
include "con0.mm"
include "csuc.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "nnon.mm"
include "onasuc.mm"
include "sylan.mm"

theorem nnasuc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A +o suc B ) = suc ( A +o B ) )

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
    coa
    co
    cA
    cB
    coa
    co
    csuc
    wceq
    cA
    nnon
    cA
    cB
    onasuc
    sylan
end
