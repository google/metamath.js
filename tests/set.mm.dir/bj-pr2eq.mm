include "wceq.mm"
include "c1o.mm"
include "bj-cproj.mm"
include "bj-cpr2.mm"
include "bj-projeq2.mm"
include "df-bj-pr2.mm"
include "3eqtr4g.mm"

theorem bj-pr2eq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> pr2 A = pr2 B )

  proof
    cA
    cB
    wceq
    c1o
    cA
    bj-cproj
    c1o
    cB
    bj-cproj
    cA
    bj-cpr2
    cB
    bj-cpr2
    c1o
    cA
    cB
    bj-projeq2
    cA
    df-bj-pr2
    cB
    df-bj-pr2
    3eqtr4g
end
