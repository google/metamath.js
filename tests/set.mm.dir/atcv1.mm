include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "w3a.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "wa.mm"
include "c0h.mm"
include "wceq.mm"
include "wi.mm"
include "breq1.mm"
include "atcv0eq.mm"
include "sylan9bbr.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "3adant1.mm"
include "imp.mm"
include "wb.mm"
include "oveq1.mm"
include "atelch.mm"
include "chjidm.mm"
include "syl.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "ibd.mm"
include "impcom.mm"
include "atcveq0.mm"
include "sylan2.mm"
include "exp32.mm"
include "com34.mm"
include "3adant2.mm"
include "impbid.mm"

theorem atcv1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. HAtoms /\ C e. HAtoms ) /\ A <oH ( B vH C ) ) -> ( A = 0H <-> B = C ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    chj
    co
    #
    ccv
    wbr
    #
    wa
    cA
    c0h
    wceq
    #
    cB
    cC
    wceq
    #
    @3
    @5
    @6
    @7
    wi
    #
    @1
    @2
    @5
    @8
    wi
    @0
    @1
    @2
    wa
    #
    @6
    @5
    @7
    @9
    @6
    @5
    @7
    wi
    @9
    @6
    wa
    @5
    @7
    @6
    @5
    c0h
    @4
    ccv
    wbr
    @9
    @7
    cA
    c0h
    @4
    ccv
    breq1
    cB
    cC
    atcv0eq
    sylan9bbr
    biimpd
    ex
    com23
    3adant1
    imp
    @3
    @5
    @7
    @6
    wi
    #
    @0
    @2
    @5
    @10
    wi
    #
    @1
    @0
    @2
    @11
    @0
    @2
    @7
    @5
    @6
    @0
    @2
    @7
    @5
    @6
    wi
    @0
    @2
    @7
    wa
    #
    wa
    @5
    @6
    @12
    @0
    @4
    cat
    wcel
    #
    @5
    @6
    wb
    @7
    @2
    @13
    @7
    @2
    @13
    @7
    @2
    @2
    @13
    wb
    @7
    @2
    wa
    #
    cC
    @4
    cat
    @14
    @4
    cC
    @7
    @2
    @4
    cC
    cC
    chj
    co
    #
    cC
    cB
    cC
    cC
    chj
    oveq1
    @2
    cC
    cch
    wcel
    @15
    cC
    wceq
    cC
    atelch
    cC
    chjidm
    syl
    sylan9eq
    eqcomd
    eleq1d
    ex
    ibd
    impcom
    cA
    @4
    atcveq0
    sylan2
    biimpd
    exp32
    com34
    imp
    3adant2
    imp
    impbid
end
