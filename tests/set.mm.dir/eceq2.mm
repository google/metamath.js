include "wceq.mm"
include "csn.mm"
include "cima.mm"
include "cec.mm"
include "imaeq1.mm"
include "df-ec.mm"
include "3eqtr4g.mm"

theorem eceq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> [ C ] A = [ C ] B )

  proof
    cA
    cB
    wceq
    cA
    cC
    csn
    #
    cima
    cB
    @0
    cima
    cC
    cA
    cec
    cC
    cB
    cec
    cA
    cB
    @0
    imaeq1
    cC
    cA
    df-ec
    cC
    cB
    df-ec
    3eqtr4g
end
