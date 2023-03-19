include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "wi.mm"
include "onelss.mm"
include "ax-mp.mm"

theorem onelssi
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On


  assert |- ( B e. A -> B C_ A )

  proof
    cA
    con0
    wcel
    cB
    cA
    wcel
    cB
    cA
    wss
    wi
    on.1
    cA
    cB
    onelss
    ax-mp
end
