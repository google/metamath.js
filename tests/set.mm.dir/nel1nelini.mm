include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "nel1nelin.mm"
include "ax-mp.mm"

theorem nel1nelini
  let cA: class A
  let cB: class B
  let cC: class C
  assume nel1nelini.1: |- -. A e. B


  assert |- -. A e. ( B i^i C )

  proof
    cA
    cB
    wcel
    wn
    cA
    cB
    cC
    cin
    wcel
    wn
    nel1nelini.1
    cA
    cB
    cC
    nel1nelin
    ax-mp
end
