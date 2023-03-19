include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "nel2nelin.mm"
include "ax-mp.mm"

theorem nel2nelini
  let cA: class A
  let cB: class B
  let cC: class C
  assume nel2nelini.1: |- -. A e. C


  assert |- -. A e. ( B i^i C )

  proof
    cA
    cC
    wcel
    wn
    cA
    cB
    cC
    cin
    wcel
    wn
    nel2nelini.1
    cA
    cB
    cC
    nel2nelin
    ax-mp
end
