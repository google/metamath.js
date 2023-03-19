include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "ssel.mm"
include "ax-mp.mm"

theorem sseli
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseli.1: |- A C_ B


  assert |- ( C e. A -> C e. B )

  proof
    cA
    cB
    wss
    cC
    cA
    wcel
    cC
    cB
    wcel
    wi
    sseli.1
    cA
    cB
    cC
    ssel
    ax-mp
end
