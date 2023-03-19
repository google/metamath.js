include "word.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cin.mm"
include "wceq.mm"
include "wne.mm"
include "wo.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "sseldd.mm"
include "ordelord.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ordtri3.mm"
include "necon2abid.mm"
include "wn.mm"
include "simpr.mm"
include "simplrl.mm"
include "elind.mm"
include "adantr.mm"
include "ordirr.mm"
include "syl.mm"
include "inss1.mm"
include "sseli.mm"
include "nsyl.mm"
include "nelne1.mm"
include "necomd.mm"
include "simplrr.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbird.mm"
include "necon4d.mm"
include "ineq1.mm"
include "impbid1.mm"

theorem fin23lem24
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( Ord A /\ B C_ A ) /\ ( C e. B /\ D e. B ) ) -> ( ( C i^i B ) = ( D i^i B ) <-> C = D ) )

  proof
    cA
    word
    #
    cB
    cA
    wss
    #
    wa
    #
    cC
    cB
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    #
    wa
    #
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    wceq
    cC
    cD
    wceq
    @6
    cC
    cD
    @7
    @8
    @6
    cC
    cD
    wne
    #
    cC
    cD
    wcel
    #
    cD
    cC
    wcel
    #
    wo
    #
    @7
    @8
    wne
    #
    @6
    cC
    word
    #
    cD
    word
    #
    @12
    @9
    wb
    @6
    @0
    cC
    cA
    wcel
    @14
    @0
    @1
    @5
    simpll
    #
    @6
    cB
    cA
    cC
    @0
    @1
    @5
    simplr
    #
    @2
    @3
    @4
    simprl
    sseldd
    cA
    cC
    ordelord
    syl2anc
    #
    @6
    @0
    cD
    cA
    wcel
    @15
    @16
    @6
    cB
    cA
    cD
    @17
    @2
    @3
    @4
    simprr
    sseldd
    cA
    cD
    ordelord
    syl2anc
    #
    @14
    @15
    wa
    @12
    cC
    cD
    cC
    cD
    ordtri3
    necon2abid
    syl2anc
    @6
    @12
    @13
    @6
    @10
    @13
    @11
    @6
    @10
    wa
    #
    @8
    @7
    @20
    cC
    @8
    wcel
    cC
    @7
    wcel
    #
    wn
    @8
    @7
    wne
    @20
    cD
    cB
    cC
    @6
    @10
    simpr
    @2
    @3
    @4
    @10
    simplrl
    elind
    @20
    cC
    cC
    wcel
    #
    @21
    @20
    @14
    @22
    wn
    @6
    @14
    @10
    @18
    adantr
    cC
    ordirr
    syl
    @7
    cC
    cC
    cC
    cB
    inss1
    sseli
    nsyl
    cC
    @8
    @7
    nelne1
    syl2anc
    necomd
    @6
    @11
    wa
    #
    cD
    @7
    wcel
    cD
    @8
    wcel
    #
    wn
    @13
    @23
    cC
    cB
    cD
    @6
    @11
    simpr
    @2
    @3
    @4
    @11
    simplrr
    elind
    @23
    cD
    cD
    wcel
    #
    @24
    @23
    @15
    @25
    wn
    @6
    @15
    @11
    @19
    adantr
    cD
    ordirr
    syl
    @8
    cD
    cD
    cD
    cB
    inss1
    sseli
    nsyl
    cD
    @7
    @8
    nelne1
    syl2anc
    jaodan
    ex
    sylbird
    necon4d
    cC
    cD
    cB
    ineq1
    impbid1
end
