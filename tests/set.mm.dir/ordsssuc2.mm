include "cvv.mm"
include "wcel.mm"
include "word.mm"
include "con0.mm"
include "wa.mm"
include "wss.mm"
include "csuc.mm"
include "wb.mm"
include "wi.mm"
include "elong.mm"
include "biimprd.mm"
include "anim1d.mm"
include "onsssuc.mm"
include "syl6.mm"
include "wn.mm"
include "annim.mm"
include "ssexg.mm"
include "ex.mm"
include "elex.mm"
include "a1d.mm"
include "pm5.21ni.mm"
include "sylbi.mm"
include "expcom.mm"
include "adantld.mm"
include "pm2.61i.mm"

theorem ordsssuc2
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ B e. On ) -> ( A C_ B <-> A e. suc B ) )

  proof
    cA
    cvv
    wcel
    #
    cA
    word
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    cB
    csuc
    #
    wcel
    #
    wb
    #
    wi
    @0
    @3
    cA
    con0
    wcel
    #
    @2
    wa
    @7
    @0
    @1
    @8
    @2
    @0
    @8
    @1
    cA
    cvv
    elong
    biimprd
    anim1d
    cA
    cB
    onsssuc
    syl6
    @0
    wn
    #
    @2
    @7
    @1
    @2
    @9
    @7
    @2
    @9
    wa
    @2
    @0
    wi
    #
    wn
    @7
    @2
    @0
    annim
    @4
    @10
    @6
    @4
    @2
    @0
    cA
    cB
    con0
    ssexg
    ex
    @6
    @0
    @2
    cA
    @5
    elex
    a1d
    pm5.21ni
    sylbi
    expcom
    adantld
    pm2.61i
end
