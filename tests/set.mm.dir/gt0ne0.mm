include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "0red.mm"
include "ltne.mm"
include "sylan.mm"

theorem gt0ne0
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A ) -> A =/= 0 )

  proof
    cA
    cr
    wcel
    #
    cc0
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    cc0
    wne
    @0
    0red
    cc0
    cA
    ltne
    sylan
end
