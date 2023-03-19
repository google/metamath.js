include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wb.mm"
include "lenlt.mm"
include "ancoms.mm"
include "con2bid.mm"

theorem ltnle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> -. B <_ A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cB
    cA
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    @1
    @0
    @2
    @3
    wn
    wb
    cB
    cA
    lenlt
    ancoms
    con2bid
end
