include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "mpbi.mm"

theorem neii
  let cA: class A
  let cB: class B
  assume neii.1: |- A =/= B


  assert |- -. A = B

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    wn
    neii.1
    cA
    cB
    df-ne
    mpbi
end
