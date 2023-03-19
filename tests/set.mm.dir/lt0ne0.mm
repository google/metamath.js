include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "ltne.mm"
include "necomd.mm"

theorem lt0ne0
  let cA: class A


  assert |- ( ( A e. RR /\ A < 0 ) -> A =/= 0 )

  proof
    cA
    cr
    wcel
    cA
    cc0
    clt
    wbr
    wa
    cc0
    cA
    cA
    cc0
    ltne
    necomd
end
