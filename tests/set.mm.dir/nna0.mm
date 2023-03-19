include "com.mm"
include "wcel.mm"
include "con0.mm"
include "c0.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "nnon.mm"
include "oa0.mm"
include "syl.mm"

theorem nna0
  let cA: class A


  assert |- ( A e. _om -> ( A +o (/) ) = A )

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    cA
    c0
    coa
    co
    cA
    wceq
    cA
    nnon
    cA
    oa0
    syl
end
