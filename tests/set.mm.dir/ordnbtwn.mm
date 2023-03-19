include "word.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "csuc.mm"
include "ordirr.mm"
include "wn.mm"
include "ordn2lp.mm"
include "wi.mm"
include "pm2.24.mm"
include "eleq2.mm"
include "biimpac.mm"
include "a1d.mm"
include "jaodan.mm"
include "syl5com.mm"
include "mtod.mm"
include "elsuci.mm"
include "anim2i.mm"
include "nsyl.mm"

theorem ordnbtwn
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
    cB
    cA
    wceq
    #
    wo
    #
    wa
    #
    @1
    cB
    cA
    csuc
    wcel
    #
    wa
    @0
    @5
    cA
    cA
    wcel
    #
    cA
    ordirr
    @0
    @1
    @2
    wa
    #
    wn
    #
    @5
    @7
    cA
    cB
    ordn2lp
    @1
    @2
    @9
    @7
    wi
    @3
    @8
    @7
    pm2.24
    @1
    @3
    wa
    @7
    @9
    @3
    @1
    @7
    cB
    cA
    cA
    eleq2
    biimpac
    a1d
    jaodan
    syl5com
    mtod
    @6
    @4
    @1
    cB
    cA
    elsuci
    anim2i
    nsyl
end
