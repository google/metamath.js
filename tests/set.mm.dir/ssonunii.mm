include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "ssonuni.mm"
include "ax-mp.mm"

theorem ssonunii
  let cA: class A
  assume ssonuni.1: |- A e. _V


  assert |- ( A C_ On -> U. A e. On )

  proof
    cA
    cvv
    wcel
    cA
    con0
    wss
    cA
    cuni
    con0
    wcel
    wi
    ssonuni.1
    cA
    cvv
    ssonuni
    ax-mp
end
