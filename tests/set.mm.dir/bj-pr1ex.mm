include "wcel.mm"
include "bj-cpr1.mm"
include "c0.mm"
include "bj-cproj.mm"
include "cvv.mm"
include "df-bj-pr1.mm"
include "bj-projex.mm"
include "syl5eqel.mm"

theorem bj-pr1ex
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> pr1 A e. _V )

  proof
    cA
    cV
    wcel
    cA
    bj-cpr1
    c0
    cA
    bj-cproj
    cvv
    cA
    df-bj-pr1
    c0
    cA
    cV
    bj-projex
    syl5eqel
end
