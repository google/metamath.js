include "cvv.mm"
include "wcel.mm"
include "word.mm"
include "csuc.mm"
include "wb.mm"
include "con0.mm"
include "elong.mm"
include "suceloni.mm"
include "eloni.mm"
include "syl.mm"
include "syl6bir.mm"
include "sucidg.mm"
include "ordelord.mm"
include "ex.mm"
include "syl5com.mm"
include "impbid.mm"
include "wn.mm"
include "wceq.mm"
include "sucprc.mm"
include "eqcomd.mm"
include "ordeq.mm"
include "pm2.61i.mm"

theorem ordsuc
  let cA: class A


  assert |- ( Ord A <-> Ord suc A )

  proof
    cA
    cvv
    wcel
    #
    cA
    word
    #
    cA
    csuc
    #
    word
    #
    wb
    #
    @0
    @1
    @3
    @0
    @1
    cA
    con0
    wcel
    #
    @3
    cA
    cvv
    elong
    @5
    @2
    con0
    wcel
    @3
    cA
    suceloni
    @2
    eloni
    syl
    syl6bir
    @0
    cA
    @2
    wcel
    #
    @3
    @1
    cA
    cvv
    sucidg
    @3
    @6
    @1
    @2
    cA
    ordelord
    ex
    syl5com
    impbid
    @0
    wn
    #
    cA
    @2
    wceq
    @4
    @7
    @2
    cA
    cA
    sucprc
    eqcomd
    cA
    @2
    ordeq
    syl
    pm2.61i
end
