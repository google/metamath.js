include "csuc.mm"
include "c0.mm"
include "wne.mm"
include "com.mm"
include "wcel.mm"
include "nsuceq0.mm"
include "a1i.mm"

theorem peano3
  let cA: class A


  assert |- ( A e. _om -> suc A =/= (/) )

  proof
    cA
    csuc
    c0
    wne
    cA
    com
    wcel
    cA
    nsuceq0
    a1i
end
