include "wcel.mm"
include "wnel.mm"
include "wn.mm"
include "df-nel.mm"
include "bicomi.mm"
include "con1bii.mm"

theorem nnel
  let cA: class A
  let cB: class B


  assert |- ( -. A e/ B <-> A e. B )

  proof
    cA
    cB
    wcel
    #
    cA
    cB
    wnel
    #
    @1
    @0
    wn
    cA
    cB
    df-nel
    bicomi
    con1bii
end
