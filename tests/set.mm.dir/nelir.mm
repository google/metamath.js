include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "df-nel.mm"
include "mpbir.mm"

theorem nelir
  let cA: class A
  let cB: class B
  assume nelir.1: |- -. A e. B


  assert |- A e/ B

  proof
    cA
    cB
    wnel
    cA
    cB
    wcel
    wn
    nelir.1
    cA
    cB
    df-nel
    mpbir
end
