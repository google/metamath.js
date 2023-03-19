include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "df-pr.mm"
include "ineq2i.mm"
include "indi.mm"
include "eqtri.mm"
include "wceq.mm"
include "ineq1i.mm"
include "indir.mm"
include "disjsn2.mm"
include "anim12i.mm"
include "un00.mm"
include "sylib.mm"
include "syl5eq.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"

theorem disjpr2
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
    #
    @7
    cC
    csn
    #
    cin
    #
    @7
    cD
    csn
    #
    cin
    #
    cun
    #
    c0
    @9
    @7
    @10
    @12
    cun
    #
    cin
    @14
    @8
    @15
    @7
    cC
    cD
    df-pr
    ineq2i
    @7
    @10
    @12
    indi
    eqtri
    @6
    @14
    c0
    c0
    cun
    c0
    @6
    @11
    c0
    @13
    c0
    @2
    @11
    c0
    wceq
    @5
    @2
    @11
    cA
    csn
    #
    @10
    cin
    #
    cB
    csn
    #
    @10
    cin
    #
    cun
    #
    c0
    @11
    @16
    @18
    cun
    #
    @10
    cin
    @20
    @7
    @21
    @10
    cA
    cB
    df-pr
    #
    ineq1i
    @16
    @18
    @10
    indir
    eqtri
    @2
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
    @0
    @23
    @1
    @24
    cA
    cC
    disjsn2
    cB
    cC
    disjsn2
    anim12i
    @17
    @19
    un00
    sylib
    syl5eq
    adantr
    @5
    @13
    c0
    wceq
    @2
    @5
    @13
    @16
    @12
    cin
    #
    @18
    @12
    cin
    #
    cun
    #
    c0
    @13
    @21
    @12
    cin
    @27
    @7
    @21
    @12
    @22
    ineq1i
    @16
    @18
    @12
    indir
    eqtri
    @5
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
    @3
    @28
    @4
    @29
    cA
    cD
    disjsn2
    cB
    cD
    disjsn2
    anim12i
    @25
    @26
    un00
    sylib
    syl5eq
    adantl
    uneq12d
    c0
    un0
    syl6eq
    syl5eq
end
