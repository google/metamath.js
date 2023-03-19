include "cnpi.mm"
include "wcel.mm"
include "com.mm"
include "con0.mm"
include "pinn.mm"
include "nnon.mm"
include "syl.mm"

theorem pion
  let cA: class A


  assert |- ( A e. N. -> A e. On )

  proof
    cA
    cnpi
    wcel
    cA
    com
    wcel
    cA
    con0
    wcel
    cA
    pinn
    cA
    nnon
    syl
end
