include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "word.mm"
include "eloni.mm"
include "ordn2lp.mm"
include "pm3.13.mm"
include "3syl.mm"
include "adantr.mm"
include "wss.mm"
include "eqimss.mm"
include "sucssel.mm"
include "syl5.mm"
include "elsuci.mm"
include "ord.mm"
include "com12.mm"
include "syl9.mm"
include "eqimss2.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "jaao.mm"
include "mpd.mm"
include "suceq.mm"
include "impbid1.mm"

theorem suc11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( suc A = suc B <-> A = B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    csuc
    #
    cB
    csuc
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @2
    cA
    cB
    wcel
    #
    wn
    #
    cB
    cA
    wcel
    #
    wn
    #
    wo
    #
    @5
    @6
    wi
    #
    @0
    @11
    @1
    @0
    cA
    word
    @7
    @9
    wa
    wn
    @11
    cA
    eloni
    cA
    cB
    ordn2lp
    @7
    @9
    pm3.13
    3syl
    adantr
    @0
    @8
    @12
    @1
    @10
    @0
    @5
    cA
    @4
    wcel
    #
    @8
    @6
    @5
    @3
    @4
    wss
    @0
    @13
    @3
    @4
    eqimss
    cA
    @4
    con0
    sucssel
    syl5
    @13
    @8
    @6
    @13
    @7
    @6
    cA
    cB
    elsuci
    ord
    com12
    syl9
    @1
    @5
    cB
    @3
    wcel
    #
    @10
    @6
    @5
    @4
    @3
    wss
    @1
    @14
    @4
    @3
    eqimss2
    cB
    @3
    con0
    sucssel
    syl5
    @14
    @10
    @6
    @14
    @10
    cB
    cA
    wceq
    #
    @6
    @14
    @9
    @15
    cB
    cA
    elsuci
    ord
    cB
    cA
    eqcom
    syl6ib
    com12
    syl9
    jaao
    mpd
    cA
    cB
    suceq
    impbid1
end
