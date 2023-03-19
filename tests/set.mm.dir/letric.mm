include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "clt.mm"
include "ltnle.mm"
include "ltle.mm"
include "sylbird.mm"
include "orrd.mm"
include "ancoms.mm"

theorem letric
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B \/ B <_ A ) )

  proof
    cB
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wo
    @0
    @1
    wa
    #
    @2
    @3
    @4
    @2
    wn
    cB
    cA
    clt
    wbr
    @3
    cB
    cA
    ltnle
    cB
    cA
    ltle
    sylbird
    orrd
    ancoms
end
