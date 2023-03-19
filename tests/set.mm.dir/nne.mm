include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "df-ne.mm"
include "con2bii.mm"
include "bicomi.mm"

theorem nne
  let cA: class A
  let cB: class B


  assert |- ( -. A =/= B <-> A = B )

  proof
    cA
    cB
    wceq
    #
    cA
    cB
    wne
    #
    wn
    @1
    @0
    cA
    cB
    df-ne
    con2bii
    bicomi
end
