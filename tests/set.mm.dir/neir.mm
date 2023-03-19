include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "mpbir.mm"

theorem neir
  let cA: class A
  let cB: class B
  assume neir.1: |- -. A = B


  assert |- A =/= B

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    wn
    neir.1
    cA
    cB
    df-ne
    mpbir
end
