include "com.mm"
include "wcel.mm"
include "con0.mm"
include "csuc.mm"
include "wceq.mm"
include "wb.mm"
include "nnon.mm"
include "suc11.mm"
include "syl2an.mm"

theorem peano4
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( suc A = suc B <-> A = B ) )

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    cB
    con0
    wcel
    cA
    csuc
    cB
    csuc
    wceq
    cA
    cB
    wceq
    wb
    cB
    com
    wcel
    cA
    nnon
    cB
    nnon
    cA
    cB
    suc11
    syl2an
end
