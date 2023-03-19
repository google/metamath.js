include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "peano2.mm"
include "cardnn.mm"
include "syl.mm"
include "suceq.mm"
include "eqtr4d.mm"

theorem cardsucnn
  let cA: class A


  assert |- ( A e. _om -> ( card ` suc A ) = suc ( card ` A ) )

  proof
    cA
    com
    wcel
    #
    cA
    csuc
    #
    ccrd
    cfv
    #
    @1
    cA
    ccrd
    cfv
    #
    csuc
    #
    @0
    @1
    com
    wcel
    @2
    @1
    wceq
    cA
    peano2
    @1
    cardnn
    syl
    @0
    @3
    cA
    wceq
    @4
    @1
    wceq
    cA
    cardnn
    @3
    cA
    suceq
    syl
    eqtr4d
end
