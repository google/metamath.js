include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "c0h.mm"
include "wne.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "atcvatlem.mm"
include "wi.mm"
include "cch.mm"
include "wceq.mm"
include "atelch.mm"
include "chjcom.mm"
include "syl2an.mm"
include "psseq2d.mm"
include "anbi2d.mm"
include "ex.mm"
include "sylbird.mm"
include "ancoms.mm"
include "imp.mm"
include "wo.mm"
include "w3a.mm"
include "wb.mm"
include "chlub.mm"
include "3comr.mm"
include "ssnpss.mm"
include "syl6bi.mm"
include "con2d.mm"
include "ianor.mm"
include "syl6ib.mm"
include "mp3an1.mm"
include "adantrl.mm"
include "mpjaod.mm"

theorem atcvati
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume atoml.1: |- A e. CH


  assert |- ( ( B e. HAtoms /\ C e. HAtoms ) -> ( ( A =/= 0H /\ A C. ( B vH C ) ) -> A e. HAtoms ) )

  proof
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    wa
    #
    cA
    c0h
    wne
    #
    cA
    cB
    cC
    chj
    co
    #
    wpss
    #
    wa
    #
    cA
    cat
    wcel
    #
    @2
    @6
    wa
    cB
    cA
    wss
    #
    wn
    #
    @7
    cC
    cA
    wss
    #
    wn
    #
    cA
    cB
    cC
    atoml.1
    atcvatlem
    @2
    @6
    @11
    @7
    wi
    #
    @1
    @0
    @6
    @12
    wi
    @1
    @0
    wa
    #
    @6
    @3
    cA
    cC
    cB
    chj
    co
    #
    wpss
    #
    wa
    #
    @12
    @13
    @15
    @5
    @3
    @13
    @14
    @4
    cA
    @1
    cC
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @14
    @4
    wceq
    @0
    cC
    atelch
    #
    cB
    atelch
    #
    cC
    cB
    chjcom
    syl2an
    psseq2d
    anbi2d
    @13
    @16
    @12
    cA
    cC
    cB
    atoml.1
    atcvatlem
    ex
    sylbird
    ancoms
    imp
    @2
    @5
    @9
    @11
    wo
    #
    @3
    @2
    @5
    @21
    @0
    @18
    @17
    @5
    @21
    wi
    #
    @1
    @20
    @19
    cA
    cch
    wcel
    #
    @18
    @17
    @22
    atoml.1
    @23
    @18
    @17
    w3a
    #
    @5
    @8
    @10
    wa
    #
    wn
    @21
    @24
    @25
    @5
    @24
    @25
    @4
    cA
    wss
    #
    @5
    wn
    @18
    @17
    @23
    @25
    @26
    wb
    cB
    cC
    cA
    chlub
    3comr
    @4
    cA
    ssnpss
    syl6bi
    con2d
    @8
    @10
    ianor
    syl6ib
    mp3an1
    syl2an
    imp
    adantrl
    mpjaod
    ex
end
