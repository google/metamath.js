include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "wceq.mm"
include "df-pr.mm"
include "a1i.mm"
include "ineq2d.mm"
include "indi.mm"
include "ineq1i.mm"
include "indir.mm"
include "eqtri.mm"
include "disjsn2.mm"
include "adantr.mm"
include "adantl.mm"
include "jca.mm"
include "un00.mm"
include "sylib.mm"
include "syl5eq.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem disjpr2OLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A =/= C /\ B =/= C ) /\ ( A =/= D /\ B =/= D ) ) -> ( { A , B } i^i { C , D } ) = (/) )

  proof
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    cA
    cD
    wne
    #
    cB
    cD
    wne
    #
    wa
    #
    wa
    #
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    cin
    @7
    cC
    csn
    #
    cD
    csn
    #
    cun
    #
    cin
    #
    c0
    @6
    @8
    @11
    @7
    @8
    @11
    wceq
    @6
    cC
    cD
    df-pr
    a1i
    ineq2d
    @6
    @12
    @7
    @9
    cin
    #
    @7
    @10
    cin
    #
    cun
    #
    c0
    @7
    @9
    @10
    indi
    @6
    @15
    c0
    c0
    cun
    c0
    @6
    @13
    c0
    @14
    c0
    @6
    @13
    cA
    csn
    #
    @9
    cin
    #
    cB
    csn
    #
    @9
    cin
    #
    cun
    #
    c0
    @13
    @16
    @18
    cun
    #
    @9
    cin
    @20
    @7
    @21
    @9
    cA
    cB
    df-pr
    #
    ineq1i
    @16
    @18
    @9
    indir
    eqtri
    @6
    @17
    c0
    wceq
    #
    @19
    c0
    wceq
    #
    wa
    @20
    c0
    wceq
    @6
    @23
    @24
    @2
    @23
    @5
    @0
    @23
    @1
    cA
    cC
    disjsn2
    adantr
    adantr
    @2
    @24
    @5
    @1
    @24
    @0
    cB
    cC
    disjsn2
    adantl
    adantr
    jca
    @17
    @19
    un00
    sylib
    syl5eq
    @6
    @14
    @16
    @10
    cin
    #
    @18
    @10
    cin
    #
    cun
    #
    c0
    @14
    @21
    @10
    cin
    @27
    @7
    @21
    @10
    @22
    ineq1i
    @16
    @18
    @10
    indir
    eqtri
    @6
    @25
    c0
    wceq
    #
    @26
    c0
    wceq
    #
    wa
    @27
    c0
    wceq
    @6
    @28
    @29
    @5
    @28
    @2
    @3
    @28
    @4
    cA
    cD
    disjsn2
    adantr
    adantl
    @5
    @29
    @2
    @4
    @29
    @3
    cB
    cD
    disjsn2
    adantl
    adantl
    jca
    @25
    @26
    un00
    sylib
    syl5eq
    uneq12d
    c0
    un0
    syl6eq
    syl5eq
    eqtrd
end
