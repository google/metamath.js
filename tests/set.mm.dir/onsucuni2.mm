include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wa.mm"
include "cuni.mm"
include "word.mm"
include "eleq1.mm"
include "biimpac.mm"
include "eloni.mm"
include "ordsuc.mm"
include "ordunisuc.mm"
include "sylbir.mm"
include "suceq.mm"
include "syl.mm"
include "eqtr4d.mm"
include "3syl.mm"
include "unieq.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "anabsi7.mm"
include "adantr.mm"
include "eqtrd.mm"

theorem onsucuni2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ A = suc B ) -> suc U. A = A )

  proof
    cA
    con0
    wcel
    #
    cA
    cB
    csuc
    #
    wceq
    #
    wa
    #
    cA
    cuni
    #
    csuc
    #
    cA
    csuc
    #
    cuni
    #
    cA
    @0
    @2
    @5
    @7
    wceq
    #
    @3
    @8
    @2
    @1
    cuni
    #
    csuc
    #
    @1
    csuc
    #
    cuni
    #
    wceq
    #
    @3
    @1
    con0
    wcel
    #
    @1
    word
    #
    @13
    @2
    @0
    @14
    cA
    @1
    con0
    eleq1
    biimpac
    @1
    eloni
    @15
    @10
    @1
    @12
    @15
    @9
    cB
    wceq
    #
    @10
    @1
    wceq
    @15
    cB
    word
    @16
    cB
    ordsuc
    cB
    ordunisuc
    sylbir
    @9
    cB
    suceq
    syl
    @1
    ordunisuc
    eqtr4d
    3syl
    @2
    @5
    @10
    @7
    @12
    @2
    @4
    @9
    wceq
    @5
    @10
    wceq
    cA
    @1
    unieq
    @4
    @9
    suceq
    syl
    @2
    @6
    @11
    cA
    @1
    suceq
    unieqd
    eqeq12d
    syl5ibr
    anabsi7
    @0
    @7
    cA
    wceq
    #
    @2
    @0
    cA
    word
    @17
    cA
    eloni
    cA
    ordunisuc
    syl
    adantr
    eqtrd
end
