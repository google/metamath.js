include "wtr.mm"
include "csuc.mm"
include "cuni.mm"
include "wceq.mm"
include "ontrci.mm"
include "con0.mm"
include "elexi.mm"
include "unisuc.mm"
include "mpbi.mm"

theorem onunisuci
  let cA: class A
  assume on.1: |- A e. On


  assert |- U. suc A = A

  proof
    cA
    wtr
    cA
    csuc
    cuni
    cA
    wceq
    cA
    on.1
    ontrci
    cA
    cA
    con0
    on.1
    elexi
    unisuc
    mpbi
end
