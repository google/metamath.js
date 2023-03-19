include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "peano2b.mm"
include "biimpi.mm"

theorem peano2
  let cA: class A


  assert |- ( A e. _om -> suc A e. _om )

  proof
    cA
    com
    wcel
    cA
    csuc
    com
    wcel
    cA
    peano2b
    biimpi
end
