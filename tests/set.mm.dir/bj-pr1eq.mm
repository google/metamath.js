include "wceq.mm"
include "c0.mm"
include "bj-cproj.mm"
include "bj-cpr1.mm"
include "bj-projeq2.mm"
include "df-bj-pr1.mm"
include "3eqtr4g.mm"

theorem bj-pr1eq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> pr1 A = pr1 B )

  proof
    cA
    cB
    wceq
    c0
    cA
    bj-cproj
    c0
    cB
    bj-cproj
    cA
    bj-cpr1
    cB
    bj-cpr1
    c0
    cA
    cB
    bj-projeq2
    cA
    df-bj-pr1
    cB
    df-bj-pr1
    3eqtr4g
end
