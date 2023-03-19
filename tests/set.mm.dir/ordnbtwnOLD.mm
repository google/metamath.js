include "word.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "csuc.mm"
include "wn.mm"
include "ordn2lp.mm"
include "ordirr.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "elsuci.mm"
include "anim2i.mm"
include "andi.mm"
include "sylib.mm"
include "eleq2.mm"
include "biimpac.mm"
include "orim2i.mm"
include "syl.mm"
include "nsyl.mm"

theorem ordnbtwnOLD
  let cA: class A
  let cB: class B


  assert |- ( Ord A -> -. ( A e. B /\ B e. suc A ) )

  proof
    cA
    word
    #
    cA
    cB
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    cA
    cA
    wcel
    #
    wo
    #
    @1
    cB
    cA
    csuc
    wcel
    #
    wa
    #
    @0
    @3
    wn
    @4
    wn
    @5
    wn
    cA
    cB
    ordn2lp
    cA
    ordirr
    @3
    @4
    ioran
    sylanbrc
    @7
    @3
    @1
    cB
    cA
    wceq
    #
    wa
    #
    wo
    #
    @5
    @7
    @1
    @2
    @8
    wo
    #
    wa
    @10
    @6
    @11
    @1
    cB
    cA
    elsuci
    anim2i
    @1
    @2
    @8
    andi
    sylib
    @9
    @4
    @3
    @8
    @1
    @4
    cB
    cA
    cA
    eleq2
    biimpac
    orim2i
    syl
    nsyl
end
