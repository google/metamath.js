include "com.mm"
include "wcel.mm"
include "con0.mm"
include "c0.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "nnon.mm"
include "om0.mm"
include "syl.mm"

theorem nnm0
  let cA: class A


  assert |- ( A e. _om -> ( A .o (/) ) = (/) )

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    cA
    c0
    comu
    co
    c0
    wceq
    cA
    nnon
    cA
    om0
    syl
end
