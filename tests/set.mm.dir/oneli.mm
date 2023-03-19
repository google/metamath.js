include "con0.mm"
include "wcel.mm"
include "onelon.mm"
include "mpan.mm"

theorem oneli
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On


  assert |- ( B e. A -> B e. On )

  proof
    cA
    con0
    wcel
    cB
    cA
    wcel
    cB
    con0
    wcel
    on.1
    cA
    cB
    onelon
    mpan
end
