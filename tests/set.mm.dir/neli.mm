include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "df-nel.mm"
include "mpbi.mm"

theorem neli
  let cA: class A
  let cB: class B
  assume neli.1: |- A e/ B


  assert |- -. A e. B

  proof
    cA
    cB
    wnel
    cA
    cB
    wcel
    wn
    neli.1
    cA
    cB
    df-nel
    mpbi
end
