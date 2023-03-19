include "wpss.mm"
include "cv.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "chj.mm"
include "co.mm"
include "chpssati.mm"
include "wcel.mm"
include "ancom.mm"
include "cch.mm"
include "wb.mm"
include "pssss.mm"
include "atelch.mm"
include "chnle.mm"
include "mpan.mm"
include "adantl.mm"
include "ibar.mm"
include "chlub.mm"
include "mp3an13.mm"
include "sylan9bb.mm"
include "anbi12d.mm"
include "syl2an.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem chrelati
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A C. B -> E. x e. HAtoms ( A C. ( A vH x ) /\ ( A vH x ) C_ B ) )

  proof
    cA
    cB
    wpss
    #
    vx
    cv
    #
    cB
    wss
    #
    @1
    cA
    wss
    wn
    #
    wa
    #
    vx
    cat
    wrex
    cA
    cA
    @1
    chj
    co
    #
    wpss
    #
    @5
    cB
    wss
    #
    wa
    #
    vx
    cat
    wrex
    vx
    cA
    cB
    chpssat.1
    chpssat.2
    chpssati
    @0
    @4
    @8
    vx
    cat
    @4
    @3
    @2
    wa
    #
    @0
    @1
    cat
    wcel
    #
    wa
    @8
    @2
    @3
    ancom
    @0
    cA
    cB
    wss
    #
    @1
    cch
    wcel
    #
    @9
    @8
    wb
    @10
    cA
    cB
    pssss
    @1
    atelch
    @11
    @12
    wa
    @3
    @6
    @2
    @7
    @12
    @3
    @6
    wb
    #
    @11
    cA
    cch
    wcel
    #
    @12
    @13
    chpssat.1
    cA
    @1
    chnle
    mpan
    adantl
    @11
    @2
    @11
    @2
    wa
    #
    @12
    @7
    @11
    @2
    ibar
    @14
    @12
    cB
    cch
    wcel
    @15
    @7
    wb
    chpssat.1
    chpssat.2
    cA
    @1
    cB
    chlub
    mp3an13
    sylan9bb
    anbi12d
    syl2an
    syl5bb
    rexbidva
    mpbid
end
