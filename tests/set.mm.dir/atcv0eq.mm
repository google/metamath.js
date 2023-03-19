include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "c0h.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "cin.mm"
include "atnemeq0.mm"
include "cch.mm"
include "wb.mm"
include "atelch.mm"
include "cvp.mm"
include "sylan.mm"
include "atcv0.mm"
include "adantr.mm"
include "biantrurd.mm"
include "3bitrd.mm"
include "wi.mm"
include "chjcl.mm"
include "h0elch.mm"
include "cvntr.mm"
include "mp3an1.mm"
include "syldan.mm"
include "syl2an.mm"
include "sylbid.mm"
include "necon4ad.mm"
include "oveq1.mm"
include "chjidm.mm"
include "syl.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "ex.mm"
include "ibd.mm"
include "syl6com.mm"
include "adantl.mm"
include "impbid.mm"

theorem atcv0eq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. HAtoms /\ B e. HAtoms ) -> ( 0H <oH ( A vH B ) <-> A = B ) )

  proof
    cA
    cat
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    #
    c0h
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    cA
    cB
    wceq
    #
    @2
    @4
    cA
    cB
    @2
    cA
    cB
    wne
    #
    c0h
    cA
    ccv
    wbr
    #
    cA
    @3
    ccv
    wbr
    #
    wa
    #
    @4
    wn
    #
    @2
    @6
    cA
    cB
    cin
    c0h
    wceq
    #
    @8
    @9
    cA
    cB
    atnemeq0
    @0
    cA
    cch
    wcel
    #
    @1
    @11
    @8
    wb
    cA
    atelch
    #
    cA
    cB
    cvp
    sylan
    @2
    @7
    @8
    @0
    @7
    @1
    cA
    atcv0
    adantr
    biantrurd
    3bitrd
    @0
    @12
    cB
    cch
    wcel
    #
    @9
    @10
    wi
    #
    @1
    @13
    cB
    atelch
    #
    @12
    @14
    @3
    cch
    wcel
    #
    @15
    cA
    cB
    chjcl
    c0h
    cch
    wcel
    @12
    @17
    @15
    h0elch
    c0h
    cA
    @3
    cvntr
    mp3an1
    syldan
    syl2an
    sylbid
    necon4ad
    @1
    @5
    @4
    wi
    @0
    @5
    @1
    @3
    cat
    wcel
    #
    @4
    @5
    @1
    @18
    @5
    @1
    @1
    @18
    wb
    @5
    @1
    wa
    #
    cB
    @3
    cat
    @19
    @3
    cB
    @5
    @1
    @3
    cB
    cB
    chj
    co
    #
    cB
    cA
    cB
    cB
    chj
    oveq1
    @1
    @14
    @20
    cB
    wceq
    @16
    cB
    chjidm
    syl
    sylan9eq
    eqcomd
    eleq1d
    ex
    ibd
    @3
    atcv0
    syl6com
    adantl
    impbid
end
