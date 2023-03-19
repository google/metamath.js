include "wtr.mm"
include "csuc.mm"
include "wcel.mm"
include "wa.mm"
include "trel.mm"
include "cvv.mm"
include "wss.mm"
include "sssucid.mm"
include "ssexg.mm"
include "mpan.mm"
include "sucidg.mm"
include "syl.mm"
include "ancri.mm"
include "impel.mm"

theorem trsuc
  let cA: class A
  let cB: class B


  assert |- ( ( Tr A /\ suc B e. A ) -> B e. A )

  proof
    cA
    wtr
    cB
    cB
    csuc
    #
    wcel
    #
    @0
    cA
    wcel
    #
    wa
    cB
    cA
    wcel
    @2
    cA
    cB
    @0
    trel
    @2
    @1
    @2
    cB
    cvv
    wcel
    #
    @1
    cB
    @0
    wss
    @2
    @3
    cB
    sssucid
    cB
    @0
    cA
    ssexg
    mpan
    cB
    cvv
    sucidg
    syl
    ancri
    impel
end
