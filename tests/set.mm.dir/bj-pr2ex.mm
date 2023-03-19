include "wcel.mm"
include "bj-cpr2.mm"
include "c1o.mm"
include "bj-cproj.mm"
include "cvv.mm"
include "df-bj-pr2.mm"
include "bj-projex.mm"
include "syl5eqel.mm"

theorem bj-pr2ex
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> pr2 A e. _V )

  proof
    cA
    cV
    wcel
    cA
    bj-cpr2
    c1o
    cA
    bj-cproj
    cvv
    cA
    df-bj-pr2
    c1o
    cA
    cV
    bj-projex
    syl5eqel
end
