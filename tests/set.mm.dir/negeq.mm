include "wceq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "oveq2.mm"
include "df-neg.mm"
include "3eqtr4g.mm"

theorem negeq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> -u A = -u B )

  proof
    cA
    cB
    wceq
    cc0
    cA
    cmin
    co
    cc0
    cB
    cmin
    co
    cA
    cneg
    cB
    cneg
    cA
    cB
    cc0
    cmin
    oveq2
    cA
    df-neg
    cB
    df-neg
    3eqtr4g
end
