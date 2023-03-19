include "wrel.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "brrelex.mm"
include "brrelex2.mm"
include "simpr.mm"
include "breldmg.mm"
include "syl3anc.mm"

theorem releldm
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( Rel R /\ A R B ) -> A e. dom R )

  proof
    cR
    wrel
    #
    cA
    cB
    cR
    wbr
    #
    wa
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @1
    cA
    cR
    cdm
    wcel
    cA
    cB
    cR
    brrelex
    cA
    cB
    cR
    brrelex2
    @0
    @1
    simpr
    cA
    cB
    cvv
    cvv
    cR
    breldmg
    syl3anc
end
