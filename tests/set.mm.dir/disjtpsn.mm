include "wne.mm"
include "w3a.mm"
include "ctp.mm"
include "csn.mm"
include "cin.mm"
include "cpr.mm"
include "cun.mm"
include "c0.mm"
include "df-tp.mm"
include "ineq1i.mm"
include "wceq.mm"
include "wa.mm"
include "disjprsn.mm"
include "3adant3.mm"
include "disjsn2.mm"
include "3ad2ant3.mm"
include "jca.mm"
include "undisj1.mm"
include "sylib.mm"
include "syl5eq.mm"

theorem disjtpsn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A =/= D /\ B =/= D /\ C =/= D ) -> ( { A , B , C } i^i { D } ) = (/) )

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
    cB
    cC
    ctp
    #
    cD
    csn
    #
    cin
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    #
    @5
    cin
    #
    c0
    @4
    @8
    @5
    cA
    cB
    cC
    df-tp
    ineq1i
    @3
    @6
    @5
    cin
    c0
    wceq
    #
    @7
    @5
    cin
    c0
    wceq
    #
    wa
    @9
    c0
    wceq
    @3
    @10
    @11
    @0
    @1
    @10
    @2
    cA
    cB
    cD
    disjprsn
    3adant3
    @2
    @0
    @11
    @1
    cC
    cD
    disjsn2
    3ad2ant3
    jca
    @6
    @7
    @5
    undisj1
    sylib
    syl5eq
end
