include "wne.mm"
include "w3a.mm"
include "ctp.mm"
include "cin.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "df-tp.mm"
include "ineq2i.mm"
include "wceq.mm"
include "wa.mm"
include "ineq1i.mm"
include "3simpa.mm"
include "disjpr2.mm"
include "syl2an.mm"
include "3adant3.mm"
include "incom.mm"
include "necom.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "disjprsn.mm"
include "syl5eq.mm"
include "jca.mm"
include "undisj1.mm"
include "sylib.mm"
include "disjtpsn.mm"
include "undisj2.mm"

theorem disjtp2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- ( ( ( A =/= D /\ B =/= D /\ C =/= D ) /\ ( A =/= E /\ B =/= E /\ C =/= E ) /\ ( A =/= F /\ B =/= F /\ C =/= F ) ) -> ( { A , B , C } i^i { D , E , F } ) = (/) )

  proof
    cA
    cD
    wne
    #
    cB
    cD
    wne
    #
    cC
    cD
    wne
    #
    w3a
    #
    cA
    cE
    wne
    #
    cB
    cE
    wne
    #
    cC
    cE
    wne
    #
    w3a
    #
    cA
    cF
    wne
    cB
    cF
    wne
    cC
    cF
    wne
    w3a
    #
    w3a
    #
    cA
    cB
    cC
    ctp
    #
    cD
    cE
    cF
    ctp
    #
    cin
    @10
    cD
    cE
    cpr
    #
    cF
    csn
    #
    cun
    #
    cin
    #
    c0
    @11
    @14
    @10
    cD
    cE
    cF
    df-tp
    ineq2i
    @9
    @10
    @12
    cin
    #
    c0
    wceq
    #
    @10
    @13
    cin
    c0
    wceq
    #
    wa
    @15
    c0
    wceq
    @9
    @17
    @18
    @9
    @16
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    #
    @12
    cin
    #
    c0
    @10
    @21
    @12
    cA
    cB
    cC
    df-tp
    ineq1i
    @9
    @19
    @12
    cin
    c0
    wceq
    #
    @20
    @12
    cin
    #
    c0
    wceq
    #
    wa
    @22
    c0
    wceq
    @9
    @23
    @25
    @3
    @7
    @23
    @8
    @3
    @0
    @1
    wa
    @4
    @5
    wa
    @23
    @7
    @0
    @1
    @2
    3simpa
    @4
    @5
    @6
    3simpa
    cA
    cB
    cD
    cE
    disjpr2
    syl2an
    3adant3
    @9
    @24
    @12
    @20
    cin
    #
    c0
    @20
    @12
    incom
    @3
    @7
    @26
    c0
    wceq
    #
    @8
    @3
    cD
    cC
    wne
    #
    cE
    cC
    wne
    #
    @27
    @7
    @2
    @0
    @28
    @1
    @2
    @28
    cC
    cD
    necom
    biimpi
    3ad2ant3
    @6
    @4
    @29
    @5
    @6
    @29
    cC
    cE
    necom
    biimpi
    3ad2ant3
    cD
    cE
    cC
    disjprsn
    syl2an
    3adant3
    syl5eq
    jca
    @19
    @20
    @12
    undisj1
    sylib
    syl5eq
    @8
    @3
    @18
    @7
    cA
    cB
    cC
    cF
    disjtpsn
    3ad2ant3
    jca
    @10
    @12
    @13
    undisj2
    sylib
    syl5eq
end
